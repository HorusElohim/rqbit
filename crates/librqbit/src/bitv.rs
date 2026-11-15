use std::{path::PathBuf, sync::Arc};

use anyhow::Context;
use bitvec::{boxed::BitBox, order::Msb0, slice::BitSlice, vec::BitVec};
use parking_lot::Mutex;
use tracing::debug_span;

use crate::{spawn_utils::BlockingSpawner, storage::filesystem::OurFileExt};

pub trait BitV: Send + Sync {
    fn as_slice(&self) -> &BitSlice<u8, Msb0>;
    fn as_slice_mut(&mut self) -> &mut BitSlice<u8, Msb0>;
    fn into_dyn(self) -> Box<dyn BitV>;
    fn as_bytes(&self) -> &[u8];
    fn flush(&mut self, flush_async: bool) -> anyhow::Result<()>;
}

pub type BoxBitV = Box<dyn BitV>;

struct DiskFlushRequest {
    generation: u64,
    snapshot: BitBox<u8, Msb0>,
}

struct DiskBitVWriter {
    file: std::fs::File,
    flushed_generation: u64,
}

impl DiskBitVWriter {
    fn persist(&mut self, request: &DiskFlushRequest) -> anyhow::Result<()> {
        // A queued asynchronous snapshot must never roll back a newer
        // synchronous completion checkpoint.
        if request.generation <= self.flushed_generation {
            return Ok(());
        }
        self.file
            .pwrite_all(0, request.snapshot.as_raw_slice())
            .context("writing piece checkpoint")?;
        self.file.sync_all().context("syncing piece checkpoint")?;
        self.flushed_generation = request.generation;
        Ok(())
    }
}

pub struct DiskBackedBitV {
    bv: BitBox<u8, Msb0>,
    flush_tx: tokio::sync::mpsc::UnboundedSender<DiskFlushRequest>,
    writer: Arc<Mutex<DiskBitVWriter>>,
    generation: u64,
}

impl Drop for DiskBackedBitV {
    fn drop(&mut self) {
        if let Err(error) = self.flush(true) {
            tracing::warn!("error flushing bitv on drop: {error:#}");
        }
    }
}

// NOTE on mmap. rqbit used it for a while, but it has issues on slow disks.
// We want writes to bitv to be instant in RAM. However when disk is slow, occasionally
// the writes stall which blocks the executor.
// Thus this separate "thread" of flushing was implemented.
impl DiskBackedBitV {
    pub async fn new(filename: PathBuf, spawner: BlockingSpawner) -> anyhow::Result<Self> {
        let buf = tokio::fs::read(&filename)
            .await
            .with_context(|| format!("error reading {filename:?}"))?;
        let bv = BitVec::from_vec(buf).into_boxed_bitslice();

        // blocking file to avoid double-buffering and double-memcpy
        let file = spawner
            .block_in_place_with_semaphore(|| {
                std::fs::OpenOptions::new()
                    .write(true)
                    .create(false)
                    .open(&filename)
            })
            .await
            .with_context(|| format!("error opening {filename:?}"))?;

        let writer = Arc::new(Mutex::new(DiskBitVWriter {
            file,
            flushed_generation: 0,
        }));
        let background_writer = writer.clone();
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<DiskFlushRequest>();
        librqbit_core::spawn_utils::spawn(
            debug_span!("diskbitv-flusher", ?filename),
            format!("DiskBackedBitV::flusher {filename:?}"),
            async move {
                loop {
                    let Some(mut req) = rx.recv().await else {
                        break;
                    };
                    while let Ok(r) = rx.try_recv() {
                        req = r;
                    }

                    if let Err(e) = spawner
                        .block_in_place_with_semaphore(|| background_writer.lock().persist(&req))
                        .await
                    {
                        tracing::error!(?filename, "error writing to bitv: {e:#}");
                        if let Err(e) = tokio::fs::remove_file(&filename).await {
                            tracing::error!(?filename, "error removing bitv: {e:#}");
                        }
                        break;
                    }
                }

                Ok::<_, anyhow::Error>(())
            },
        );
        Ok(Self {
            bv,
            flush_tx: tx,
            writer,
            generation: 0,
        })
    }
}

#[async_trait::async_trait]
impl BitV for BitBox<u8, Msb0> {
    fn as_slice(&self) -> &BitSlice<u8, Msb0> {
        self.as_bitslice()
    }

    fn as_slice_mut(&mut self) -> &mut BitSlice<u8, Msb0> {
        self.as_mut_bitslice()
    }

    fn as_bytes(&self) -> &[u8] {
        self.as_raw_slice()
    }

    fn flush(&mut self, _flush_async: bool) -> anyhow::Result<()> {
        Ok(())
    }

    fn into_dyn(self) -> Box<dyn BitV> {
        Box::new(self)
    }
}

impl BitV for DiskBackedBitV {
    fn as_slice(&self) -> &BitSlice<u8, Msb0> {
        self.bv.as_bitslice()
    }

    fn as_slice_mut(&mut self) -> &mut BitSlice<u8, Msb0> {
        self.bv.as_mut_bitslice()
    }

    fn as_bytes(&self) -> &[u8] {
        self.bv.as_raw_slice()
    }

    fn flush(&mut self, flush_async: bool) -> anyhow::Result<()> {
        self.generation = self
            .generation
            .checked_add(1)
            .context("piece checkpoint generation exhausted")?;
        let req = DiskFlushRequest {
            generation: self.generation,
            snapshot: self.bv.clone(),
        };
        if flush_async {
            return self.flush_tx.send(req).context("flusher task is dead");
        }
        // Completion must acknowledge persistence, including fsync. Do not
        // wait for the async task: that deadlocks a single-threaded runtime.
        self.writer.lock().persist(&req)
    }

    fn into_dyn(self) -> Box<dyn BitV> {
        Box::new(self)
    }
}

impl BitV for Box<dyn BitV> {
    fn as_slice(&self) -> &BitSlice<u8, Msb0> {
        (**self).as_slice()
    }

    fn as_slice_mut(&mut self) -> &mut BitSlice<u8, Msb0> {
        (**self).as_slice_mut()
    }

    fn as_bytes(&self) -> &[u8] {
        (**self).as_bytes()
    }

    fn flush(&mut self, flush_async: bool) -> anyhow::Result<()> {
        (**self).flush(flush_async)
    }

    fn into_dyn(self) -> Box<dyn BitV> {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(generation: u64, byte: u8) -> DiskFlushRequest {
        DiskFlushRequest {
            generation,
            snapshot: BitVec::from_vec(vec![byte]).into_boxed_bitslice(),
        }
    }

    #[test]
    fn queued_old_snapshots_cannot_replace_a_newer_completion_checkpoint() {
        let file = tempfile::NamedTempFile::new().unwrap();
        let mut writer = DiskBitVWriter {
            file: file.reopen().unwrap(),
            flushed_generation: 0,
        };
        writer.persist(&request(2, 0xc0)).unwrap();
        writer.persist(&request(1, 0x80)).unwrap();
        assert_eq!(std::fs::read(file.path()).unwrap(), [0xc0]);
        assert_eq!(writer.flushed_generation, 2);
    }

    #[test]
    fn failed_checkpoint_writes_do_not_acknowledge_the_generation() {
        let file = tempfile::NamedTempFile::new().unwrap();
        std::fs::write(file.path(), [0_u8]).unwrap();
        let mut writer = DiskBitVWriter {
            file: std::fs::File::open(file.path()).unwrap(),
            flushed_generation: 0,
        };
        assert!(writer.persist(&request(1, 0x80)).is_err());
        assert_eq!(writer.flushed_generation, 0);
        assert_eq!(std::fs::read(file.path()).unwrap(), [0]);
    }
}
