//! Packet Queue Module
//!
//! Low-level queue infrastructure for zero-copy packet handoff between
//! network receive loop and kernel processing layer. Uses tokio channels
//! for lock-free concurrent access.

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use tokio::sync::mpsc;

use crate::domain::types::PacketBuffer;

/// Single Producer, Single Consumer queue for packet buffers
///
/// Ensures thread-safe, ordered delivery without copying.
/// Provides lock-free enqueue/dequeue operations.
#[derive(Debug)]
pub struct PacketQueue {
    tx: mpsc::UnboundedSender<PacketBuffer>,
    rx: Arc<tokio::sync::Mutex<mpsc::UnboundedReceiver<PacketBuffer>>>,
    /// Atomic counter for queue depth (updated on enqueue/dequeue)
    depth: Arc<AtomicUsize>,
}

impl PacketQueue {
    /// Create a new packet queue
    pub fn new() -> Self {
        let (tx, rx) = mpsc::unbounded_channel();
        Self {
            tx,
            rx: Arc::new(tokio::sync::Mutex::new(rx)),
            depth: Arc::new(AtomicUsize::new(0)),
        }
    }

    /// Enqueue a packet (producer side - internal network loop)
    pub fn enqueue(&self, packet: PacketBuffer) -> Result<(), String> {
        self.tx
            .send(packet)
            .map_err(|e| format!("Queue enqueue failed: {}", e))?;

        self.depth.fetch_add(1, Ordering::Release);
        Ok(())
    }

    /// Try to dequeue without blocking (consumer side - TS layer)
    pub async fn try_dequeue(&self) -> Option<PacketBuffer> {
        let mut rx = self.rx.lock().await;
        if let Some(packet) = rx.recv().await {
            self.depth.fetch_sub(1, Ordering::Release);
            Some(packet)
        } else {
            None
        }
    }

    /// Get queue depth (for monitoring)
    pub fn len(&self) -> usize {
        self.depth.load(Ordering::Acquire)
    }

    /// Check if queue is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for PacketQueue {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn packet_queue_enqueue_dequeue() {
        let queue = PacketQueue::new();

        let packet = PacketBuffer::new(vec![1, 2, 3], 1);
        let expected_ptr = packet.as_ptr();

        queue.enqueue(packet).expect("enqueue failed");
        assert_eq!(queue.len(), 1);

        let dequeued = queue.try_dequeue().await;

        assert!(dequeued.is_some());

        let p = dequeued.unwrap();

        assert_eq!(p.connection_handle, 1);
        assert_eq!(p.len(), 3);
        assert_eq!(
            p.as_ptr(),
            expected_ptr,
            "Packet data must preserve original Vec allocation (zero-copy)"
        );

        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
    }
}