use anyhow::{Context, bail};
use bstr::BStr;
use futures::{StreamExt, TryFutureExt, stream::FuturesUnordered};
use librqbit_dualstack_sockets::{BindDevice, UdpSocket};
use network_interface::{NetworkInterface, NetworkInterfaceConfig};
use reqwest::Client;
use serde_derive::Deserialize;
use std::{
    collections::HashSet,
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4},
    time::Duration,
};
use tokio::sync::mpsc::{UnboundedSender, unbounded_channel};
use tracing::{Instrument, Span, debug, debug_span, trace, warn};
use url::Url;

/// WAN connection services that lease port mappings. A gateway must be
/// addressed by the exact type it lists: IGD v2 routers (common on current ISP
/// boxes) list only `WANIPConnection:2`, and PPPoE routers `WANPPPConnection:1`.
const PORT_MAPPING_SERVICE_TYPES: [&str; 3] = [
    "urn:schemas-upnp-org:service:WANIPConnection:1",
    "urn:schemas-upnp-org:service:WANIPConnection:2",
    "urn:schemas-upnp-org:service:WANPPPConnection:1",
];
const SSDP_MULTICAST_IP: SocketAddr =
    SocketAddr::V4(SocketAddrV4::new(Ipv4Addr::new(239, 255, 255, 250), 1900));
pub const SSDP_SEARCH_WAN_IPCONNECTION_ST: &str = "urn:schemas-upnp-org:service:WANIPConnection:1";
pub const SSDP_SEARCH_ROOT_ST: &str = "upnp:rootdevice";
/// Every IGD v1 and v2 gateway answers this, whichever connection service it
/// carries; a `WANIPConnection` search misses PPP-only gateways.
pub const SSDP_SEARCH_GATEWAY_ST: &str = "urn:schemas-upnp-org:device:InternetGatewayDevice:1";

pub fn make_ssdp_search_request(kind: &str) -> String {
    format!(
        "M-SEARCH * HTTP/1.1\r\n\
            Host: 239.255.255.250:1900\r\n\
            Man: \"ssdp:discover\"\r\n\
            MX: 3\r\n\
            ST: {kind}\r\n\
            \r\n"
    )
}

pub fn get_local_ip_relative_to(
    local_dest: SocketAddr,
    interfaces: &[NetworkInterface],
) -> anyhow::Result<IpAddr> {
    fn masked_v4(ip: Ipv4Addr, mask: Ipv4Addr) -> u32 {
        ip.to_bits() & mask.to_bits()
    }

    fn masked_v6(ip: Ipv6Addr, mask: Ipv6Addr) -> u128 {
        ip.to_bits() & mask.to_bits()
    }

    for i in interfaces {
        for addr in i.addr.iter() {
            match (local_dest, addr.ip(), addr.netmask()) {
                // We are connecting to ourselves, return itself.
                (l, a, _) if l.ip() == a => return Ok(addr.ip()),
                // IPv4 masks match.
                (SocketAddr::V4(l), IpAddr::V4(a), Some(IpAddr::V4(m)))
                    if masked_v4(*l.ip(), m) == masked_v4(a, m) =>
                {
                    return Ok(addr.ip());
                }
                // Return IPv6 link-local addresses when source is link-local address and there's a scope_id set.
                (SocketAddr::V6(l), IpAddr::V6(a), _)
                    if l.ip().is_unicast_link_local() && l.scope_id() > 0 =>
                {
                    if a.is_unicast_link_local() && l.scope_id() == i.index {
                        return Ok(addr.ip());
                    }
                }
                // If V6 masks match, return.
                (SocketAddr::V6(l), IpAddr::V6(a), Some(IpAddr::V6(m)))
                    if masked_v6(*l.ip(), m) == masked_v6(a, m) =>
                {
                    return Ok(addr.ip());
                }
                // For IPv6 fallback to returning a random (first encountered) IPv6 address.
                (SocketAddr::V6(_), IpAddr::V6(_), None) => return Ok(addr.ip()),
                _ => continue,
            }
        }
    }
    bail!("couldn't find a local ip address")
}

async fn forward_port(
    connection: &WanConnection,
    local_ip: IpAddr,
    port: u16,
    lease_duration: Duration,
) -> anyhow::Result<()> {
    let arguments = format!(
        "<NewRemoteHost></NewRemoteHost>\
         <NewExternalPort>{port}</NewExternalPort>\
         <NewProtocol>TCP</NewProtocol>\
         <NewInternalPort>{port}</NewInternalPort>\
         <NewInternalClient>{local_ip}</NewInternalClient>\
         <NewEnabled>1</NewEnabled>\
         <NewPortMappingDescription>rust UPnP</NewPortMappingDescription>\
         <NewLeaseDuration>{}</NewLeaseDuration>",
        lease_duration.as_secs()
    );
    let (status, response_text) = soap_request(connection, "AddPortMapping", &arguments).await?;
    trace!(status = %status, text=response_text, "AddPortMapping response");
    if !status.is_success() {
        bail!("failed port forwarding: {}", status);
    } else {
        debug!(%local_ip, port, "successfully port forwarded");
    }
    Ok(())
}

/// Calls one action on a WAN connection service, addressed by its own type.
async fn soap_request(
    connection: &WanConnection,
    action: &str,
    arguments: &str,
) -> anyhow::Result<(reqwest::StatusCode, String)> {
    let service_type = connection.service_type;
    let request_body = format!(
        r#"<?xml version="1.0"?>
        <s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/"
            s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
            <s:Body><u:{action} xmlns:u="{service_type}">{arguments}</u:{action}></s:Body>
        </s:Envelope>"#
    );
    let response = Client::new()
        .post(connection.control_url.clone())
        .header("Content-Type", "text/xml")
        .header("SOAPAction", format!("\"{service_type}#{action}\""))
        .body(request_body)
        .send()
        .await
        .context("error sending")?;
    let status = response.status();
    let text = response
        .text()
        .await
        .context("error reading response text")?;
    Ok((status, text))
}

/// The text of the first `<tag>` element in a SOAP body. UPnP response
/// arguments are unqualified, though some gateways add attributes.
fn soap_value<'a>(body: &'a str, tag: &str) -> Option<&'a str> {
    let open = format!("<{tag}");
    let mut from = 0;
    let start = loop {
        let at = from + body[from..].find(&open)? + open.len();
        match body[at..].chars().next()? {
            '>' => break at + 1,
            c if c.is_whitespace() => break at + body[at..].find('>')? + 1,
            _ => from = at,
        }
    };
    let end = body[start..].find(&format!("</{tag}>"))?;
    Some(body[start..start + end].trim())
}

/// A WAN connection service a gateway lists, addressed by the type it lists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WanConnection {
    pub control_url: Url,
    pub service_type: &'static str,
}

/// A TCP port mapping a gateway holds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortMapping {
    pub internal_client: IpAddr,
    pub internal_port: u16,
    pub enabled: bool,
}

impl WanConnection {
    /// The gateway's own internet-facing address.
    pub async fn external_ip(&self) -> anyhow::Result<IpAddr> {
        let (status, body) = soap_request(self, "GetExternalIPAddress", "").await?;
        if !status.is_success() {
            bail!("GetExternalIPAddress failed: {status}");
        }
        soap_value(&body, "NewExternalIPAddress")
            .context("missing NewExternalIPAddress")?
            .parse()
            .context("bad NewExternalIPAddress")
    }

    /// The TCP mapping this gateway holds for `external_port`, if any.
    pub async fn tcp_port_mapping(
        &self,
        external_port: u16,
    ) -> anyhow::Result<Option<PortMapping>> {
        let arguments = format!(
            "<NewRemoteHost></NewRemoteHost>\
             <NewExternalPort>{external_port}</NewExternalPort>\
             <NewProtocol>TCP</NewProtocol>"
        );
        let (status, body) = soap_request(self, "GetSpecificPortMappingEntry", &arguments).await?;
        parse_port_mapping(status.is_success(), &body)
    }
}

fn parse_port_mapping(success: bool, body: &str) -> anyhow::Result<Option<PortMapping>> {
    if !success {
        // UPnP error 714, NoSuchEntryInArray: the gateway holds no such mapping.
        if soap_value(body, "errorCode") == Some("714") {
            return Ok(None);
        }
        bail!(
            "GetSpecificPortMappingEntry failed: {}",
            soap_value(body, "errorDescription").unwrap_or("unknown error")
        );
    }
    let value = |tag| soap_value(body, tag).with_context(|| format!("missing {tag}"));
    Ok(Some(PortMapping {
        internal_client: value("NewInternalClient")?.parse()?,
        internal_port: value("NewInternalPort")?.parse()?,
        enabled: !matches!(value("NewEnabled")?, "0" | "false"),
    }))
}

/// Every WAN connection service on this network, gathered for `timeout` from
/// every gateway that answers — not only the first: an access point running
/// its own UPnP can answer before the router that matters.
pub async fn discover_wan_connections(
    timeout: Duration,
    bind_device: Option<&BindDevice>,
) -> anyhow::Result<Vec<WanConnection>> {
    let (tx, mut rx) = unbounded_channel();
    discover_once(&tx, SSDP_SEARCH_GATEWAY_ST, timeout, bind_device).await?;
    let mut locations = Vec::new();
    while let Ok(response) = rx.try_recv() {
        if !locations.contains(&response.location) {
            locations.push(response.location);
        }
    }
    let described = futures::future::join_all(locations.into_iter().map(|location| async move {
        let description = tokio::time::timeout(timeout, discover_services(location.clone()))
            .await
            .ok()?
            .inspect_err(|e| debug!("error describing {location}: {e:#}"))
            .ok()?;
        let span = debug_span!("upnp_gateway", location = %location);
        Some(
            wan_connections(&location, &description, span)
                .map(|(_, connection)| connection)
                .collect::<Vec<_>>(),
        )
    }))
    .await;
    Ok(described.into_iter().flatten().flatten().collect())
}

/// The WAN connection services a gateway's description lists.
fn wan_connections<'a>(
    location: &'a Url,
    description: &'a RootDesc,
    span: Span,
) -> impl Iterator<Item = (Span, WanConnection)> + 'a {
    description
        .devices
        .iter()
        .flat_map(move |device| device.iter_services(span.clone()))
        .filter_map(|(span, service)| {
            let service_type = PORT_MAPPING_SERVICE_TYPES
                .into_iter()
                .find(|known| *known == service.service_type)?;
            Some((span, service, service_type))
        })
        .filter_map(move |(span, service, service_type)| {
            match location.join(&service.control_url) {
                Ok(control_url) => Some((
                    span,
                    WanConnection {
                        control_url,
                        service_type,
                    },
                )),
                Err(e) => {
                    debug!("bad control url: {e:#}");
                    None
                }
            }
        })
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
pub struct RootDesc {
    #[serde(rename = "device")]
    pub devices: Vec<Device>,
}

#[derive(Default, Clone, Debug, Deserialize, PartialEq, Eq)]
pub struct DeviceList {
    #[serde(rename = "device")]
    pub devices: Vec<Device>,
}

#[derive(Debug, Clone, Deserialize, PartialEq, Eq)]
pub struct Device {
    #[serde(rename = "deviceType")]
    pub device_type: String,
    #[serde(rename = "friendlyName", default)]
    pub friendly_name: String,
    #[serde(rename = "serviceList", default)]
    pub service_list: ServiceList,
    #[serde(rename = "deviceList", default)]
    pub device_list: DeviceList,
}

impl Device {
    pub fn iter_services(
        &self,
        parent: Span,
    ) -> Box<dyn Iterator<Item = (tracing::Span, &Service)> + '_> {
        let self_span = self.span(parent);
        let services = self.service_list.services.iter().map({
            let self_span = self_span.clone();
            move |s| (s.span(self_span.clone()), s)
        });
        Box::new(services.chain(self.device_list.devices.iter().flat_map({
            let self_span = self_span.clone();
            move |d| d.iter_services(self_span.clone())
        })))
    }

    pub fn span(&self, parent: tracing::Span) -> tracing::Span {
        debug_span!(parent: parent, "device", device = self.name())
    }
}

impl Device {
    pub fn name(&self) -> &str {
        if self.friendly_name.is_empty() {
            return &self.device_type;
        }
        &self.friendly_name
    }
}

#[derive(Clone, Debug, Deserialize, Default, PartialEq, Eq)]
pub struct ServiceList {
    #[serde(rename = "service", default)]
    pub services: Vec<Service>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
pub struct Service {
    #[serde(rename = "serviceType")]
    pub service_type: String,
    #[serde(rename = "controlURL")]
    pub control_url: String,
    #[serde(rename = "SCPDURL")]
    pub scpd_url: String,
    #[serde(rename = "eventSubURL", default)]
    pub event_sub_url: Option<String>,
}

impl Service {
    pub fn span(&self, parent: tracing::Span) -> tracing::Span {
        debug_span!(parent: parent, "service", url = self.control_url)
    }
}

#[derive(Debug)]
struct UpnpEndpoint {
    discover_response: UpnpDiscoverResponse,
    data: RootDesc,
    nics: Vec<NetworkInterface>,
}

impl UpnpEndpoint {
    fn location(&self) -> &Url {
        &self.discover_response.location
    }

    fn span(&self) -> tracing::Span {
        debug_span!("upnp_endpoint", location = %self.location())
    }

    fn my_local_ip(&self) -> anyhow::Result<IpAddr> {
        let received_from = self.discover_response.received_from;
        let local_ip = get_local_ip_relative_to(received_from, &self.nics)
            .with_context(|| format!("can't determine local IP relative to {received_from}"))?;
        Ok(local_ip)
    }

    fn port_mapping_services(&self) -> impl Iterator<Item = (Span, WanConnection)> + '_ {
        wan_connections(self.location(), &self.data, self.span())
    }
}

#[derive(Debug)]
pub struct UpnpDiscoverResponse {
    pub received_from: SocketAddr,
    pub location: Url,
}

pub async fn discover_services(location: Url) -> anyhow::Result<RootDesc> {
    let response = Client::new()
        .get(location.clone())
        .send()
        .await
        .context("failed to send GET request")?
        .text()
        .await
        .context("failed to read response body")?;
    trace!("received from {location}: {response}");
    let root_desc: RootDesc = quick_xml::de::from_str(&response)
        .context("failed to parse response body as xml")
        .inspect_err(|e| {
            debug!("failed to parse this XML: {response}. Error: {e:#}");
        })?;
    Ok(root_desc)
}

pub fn parse_upnp_discover_response(
    buf: &[u8],
    received_from: SocketAddr,
) -> anyhow::Result<UpnpDiscoverResponse> {
    let mut headers = [httparse::EMPTY_HEADER; 16];
    let mut resp = httparse::Response::new(&mut headers);
    resp.parse(buf).context("error parsing response")?;

    trace!(?resp, "parsed SSDP response");
    match resp.code {
        Some(200) => {}
        other => anyhow::bail!("bad response code {other:?}, expected 200"),
    }
    let mut location = None;
    for header in resp.headers {
        match header.name {
            "location" | "LOCATION" | "Location" => {
                location = Some(
                    std::str::from_utf8(header.value).context("bad utf-8 in location header")?,
                )
            }
            _ => continue,
        }
    }
    let location = location.context("missing location header")?;
    let location =
        Url::parse(location).with_context(|| format!("failed parsing location {location}"))?;
    Ok(UpnpDiscoverResponse {
        location,
        received_from,
    })
}

pub async fn discover_once(
    tx: &UnboundedSender<UpnpDiscoverResponse>,
    kind: &str,
    timeout: Duration,
    bind_device: Option<&BindDevice>,
) -> anyhow::Result<()> {
    // TODO: do we need IPv6 support here? I can't test it, don't have the hardware for it (router / IPv6 provider).
    let socket = UdpSocket::bind_udp(
        (Ipv4Addr::UNSPECIFIED, 0).into(),
        librqbit_dualstack_sockets::BindOpts {
            device: bind_device,
            ..Default::default()
        },
    )?;

    let message = make_ssdp_search_request(kind);
    socket
        .send_to(message.as_bytes(), SSDP_MULTICAST_IP)
        .await
        .with_context(|| format!("failed to send SSDP search request to {SSDP_MULTICAST_IP}"))?;

    let mut buffer = [0; 2048];

    let timeout = tokio::time::sleep(timeout);
    let mut timed_out = false;
    tokio::pin!(timeout);

    let mut discovered = 0;

    while !timed_out {
        tokio::select! {
            _ = &mut timeout, if !timed_out => {
                timed_out = true;
            }
            Ok((len, addr)) = socket.recv_from(&mut buffer), if !timed_out => {
                let response = &buffer[..len];
                match parse_upnp_discover_response(response, addr) {
                    Ok(r) => {
                        tx.send(r)?;
                        discovered += 1;
                    },
                    Err(e) => warn!(response=?BStr::new(response), "failed to parse SSDP response: {e:#}"),
                };
            },
        }
    }

    debug!("discovered {discovered} endpoints");
    Ok(())
}

pub struct UpnpPortForwarderOptions {
    pub lease_duration: Duration,
    pub discover_interval: Duration,
    pub discover_timeout: Duration,
}

impl Default for UpnpPortForwarderOptions {
    fn default() -> Self {
        Self {
            discover_interval: Duration::from_secs(60),
            discover_timeout: Duration::from_secs(10),
            lease_duration: Duration::from_secs(60),
        }
    }
}

pub struct UpnpPortForwarder {
    ports: Vec<u16>,
    opts: UpnpPortForwarderOptions,
    bind_device: Option<BindDevice>,
}

impl UpnpPortForwarder {
    pub fn new(
        ports: Vec<u16>,
        opts: Option<UpnpPortForwarderOptions>,
        bind_device: Option<BindDevice>,
    ) -> anyhow::Result<Self> {
        if ports.is_empty() {
            bail!("empty ports")
        }
        Ok(Self {
            ports,
            opts: opts.unwrap_or_default(),
            bind_device,
        })
    }

    async fn parse_endpoint(
        &self,
        discover_response: UpnpDiscoverResponse,
    ) -> anyhow::Result<UpnpEndpoint> {
        let services = discover_services(discover_response.location.clone()).await?;
        let nics = network_interface::NetworkInterface::show()
            .context("error listing network interfaces")?;
        Ok(UpnpEndpoint {
            discover_response,
            data: services,
            nics,
        })
    }

    async fn discover_once(
        &self,
        tx: &UnboundedSender<UpnpDiscoverResponse>,
    ) -> anyhow::Result<()> {
        discover_once(
            tx,
            SSDP_SEARCH_GATEWAY_ST,
            self.opts.discover_timeout,
            self.bind_device.as_ref(),
        )
        .await
    }

    async fn discovery(&self, tx: UnboundedSender<UpnpDiscoverResponse>) -> anyhow::Result<()> {
        let mut discover_interval = tokio::time::interval(self.opts.discover_interval);
        discover_interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);

        loop {
            discover_interval.tick().await;
            if let Err(e) = self.discover_once(&tx).await {
                warn!("failed to run SSDP/UPNP discovery: {e:#}");
            }
        }
    }

    async fn manage_port(&self, connection: &WanConnection, local_ip: IpAddr, port: u16) -> ! {
        let lease_duration = self.opts.lease_duration;
        let mut interval = tokio::time::interval(lease_duration / 2);
        interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);

        loop {
            interval.tick().await;
            if let Err(e) = forward_port(connection, local_ip, port, lease_duration).await {
                warn!("failed to forward port: {e:#}");
            }
        }
    }

    async fn manage_service(
        &self,
        connection: WanConnection,
        local_ip: IpAddr,
    ) -> anyhow::Result<()> {
        futures::future::join_all(self.ports.iter().cloned().map(|port| {
            self.manage_port(&connection, local_ip, port)
                .instrument(debug_span!("manage_port", port = port))
        }))
        .await;
        Ok(())
    }

    pub async fn run_forever(self) -> ! {
        let (discover_tx, mut discover_rx) = unbounded_channel();
        let discovery = self.discovery(discover_tx);

        let mut spawned_tasks = HashSet::<Url>::new();

        let mut endpoints = FuturesUnordered::new();
        let mut service_managers = FuturesUnordered::new();

        tokio::pin!(discovery);

        loop {
            tokio::select! {
                _ = &mut discovery => {},
                r = discover_rx.recv() => {
                    let r = r.unwrap();
                    let location = r.location.clone();
                    endpoints.push(self.parse_endpoint(r).map_err(|e| {
                        debug!("error parsing endpoint: {e:#}");
                        e
                    }).instrument(debug_span!("parse endpoint", location=location.to_string())));
                },
                Some(Ok(endpoint)) = endpoints.next(), if !endpoints.is_empty() => {
                    let mut local_ip = None;
                    for (span, connection) in endpoint.port_mapping_services() {
                        if spawned_tasks.contains(&connection.control_url) {
                            debug!("already spawned for {}", connection.control_url);
                            continue;
                        }
                        let ip = match local_ip {
                            Some(ip) => ip,
                            None => {
                                match endpoint.my_local_ip() {
                                    Ok(ip) => {
                                        local_ip = Some(ip);
                                        ip
                                    },
                                    Err(e) => {
                                        warn!("failed to determine local IP for endpoint at {}: {:#}", endpoint.location(), e);
                                        break;
                                    }
                                }
                            }
                        };
                        spawned_tasks.insert(connection.control_url.clone());
                        service_managers.push(self.manage_service(connection, ip).instrument(span))
                    }
                },
                _ = service_managers.next(), if !service_managers.is_empty() => {

                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use quick_xml::de::from_str;

    use crate::{
        Device, DeviceList, PortMapping, RootDesc, Service, ServiceList, UpnpDiscoverResponse,
        UpnpEndpoint, parse_port_mapping, soap_value,
    };

    fn endpoint(description: &str) -> UpnpEndpoint {
        UpnpEndpoint {
            discover_response: UpnpDiscoverResponse {
                received_from: "192.168.1.254:1900".parse().unwrap(),
                location: "http://192.168.1.254:38151/rootDesc.xml".parse().unwrap(),
            },
            data: from_str(description).unwrap(),
            nics: Vec::new(),
        }
    }

    fn port_mapping_services(description: &str) -> Vec<(String, &'static str)> {
        endpoint(description)
            .port_mapping_services()
            .map(|(_, connection)| (connection.control_url.to_string(), connection.service_type))
            .collect()
    }

    #[test]
    fn soap_values_are_read_with_or_without_attributes() {
        let body = r#"<u:R><NewExternalIPAddressX>no</NewExternalIPAddressX><NewExternalIPAddress xmlns:dt="urn:schemas-microsoft-com:datatypes" dt:dt="string"> 203.0.113.9 </NewExternalIPAddress></u:R>"#;
        assert_eq!(
            soap_value(body, "NewExternalIPAddress"),
            Some("203.0.113.9")
        );
        assert_eq!(soap_value("<a>1</a>", "b"), None);
    }

    #[test]
    fn a_missing_mapping_is_absent_not_an_error() {
        let held = "<NewInternalPort>6881</NewInternalPort><NewInternalClient>192.168.1.5</NewInternalClient><NewEnabled>1</NewEnabled>";
        assert_eq!(
            parse_port_mapping(true, held).unwrap(),
            Some(PortMapping {
                internal_client: "192.168.1.5".parse().unwrap(),
                internal_port: 6881,
                enabled: true,
            })
        );
        let absent =
            "<errorCode>714</errorCode><errorDescription>NoSuchEntryInArray</errorDescription>";
        assert_eq!(parse_port_mapping(false, absent).unwrap(), None);
        let refused =
            "<errorCode>606</errorCode><errorDescription>Action not authorized</errorDescription>";
        assert!(parse_port_mapping(false, refused).is_err());
    }

    #[test]
    fn igd_v1_gateway_maps_through_its_wan_ip_connection() {
        assert_eq!(
            port_mapping_services(include_str!("resources/test/devices-0.xml")),
            [(
                "http://192.168.1.254:38151/upnp/control/WANIPConnection0".to_owned(),
                "urn:schemas-upnp-org:service:WANIPConnection:1"
            )]
        );
    }

    #[test]
    fn igd_v2_gateway_maps_through_the_v2_service_it_lists() {
        assert_eq!(
            port_mapping_services(include_str!("resources/test/igd-v2.xml")),
            [(
                "http://192.168.1.254:38151/ctl/IPConn".to_owned(),
                "urn:schemas-upnp-org:service:WANIPConnection:2"
            )]
        );
    }

    #[test]
    fn test_parse_root_desc() {
        let actual = from_str::<RootDesc>(include_str!("resources/test/devices-0.xml")).unwrap();
        let expected = RootDesc {
            devices: vec![Device {
                device_type: "urn:schemas-upnp-org:device:InternetGatewayDevice:1".into(),
                friendly_name: "ARRIS TG3492LG".into(),
                service_list: ServiceList {
                    services: vec![Service {
                        service_type: "urn:schemas-upnp-org:service:Layer3Forwarding:1".into(),
                        control_url: "/upnp/control/Layer3Forwarding".into(),
                        scpd_url: "/Layer3ForwardingSCPD.xml".into(),
                        event_sub_url: Some("/upnp/event/Layer3Forwarding".into()),
                    }],
                },
                device_list: DeviceList {
                    devices: vec![Device {
                        device_type: "urn:schemas-upnp-org:device:WANDevice:1".into(),
                        friendly_name: "WANDevice:1".into(),
                        service_list: ServiceList {
                            services: vec![Service {
                                service_type:
                                    "urn:schemas-upnp-org:service:WANCommonInterfaceConfig:1".into(),
                                control_url: "/upnp/control/WANCommonInterfaceConfig0".into(),
                                scpd_url: "/WANCommonInterfaceConfigSCPD.xml".into(),
                                event_sub_url: Some("/upnp/event/WANCommonInterfaceConfig0".into()),
                            }],
                        },
                        device_list: DeviceList {
                            devices: vec![Device {
                                device_type: "urn:schemas-upnp-org:device:WANConnectionDevice:1"
                                    .into(),
                                friendly_name: "WANConnectionDevice:1".into(),
                                service_list: ServiceList {
                                    services: vec![Service {
                                        service_type:
                                            "urn:schemas-upnp-org:service:WANIPConnection:1".into(),
                                        control_url: "/upnp/control/WANIPConnection0".into(),
                                        scpd_url: "/WANIPConnectionServiceSCPD.xml".into(),
                                        event_sub_url: Some("/upnp/event/WANIPConnection0".into()),
                                    }],
                                },
                                device_list: DeviceList { devices: vec![] },
                            }],
                        },
                    }],
                },
            }],
        };
        assert_eq!(actual, expected);
    }
}
