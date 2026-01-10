//! Production Backend Implementation
//!
//! # Design
//! This backend is optimized for **production runtime performance**:
//! - Uses `BinaryHeap` for O(log n) event insertion and extraction
//! - Thread-safe with `RwLock` for concurrent access
//! - Heap-allocated for dynamic scalability
//!
//! # Why Not Kani-Friendly?
//! - `BinaryHeap` uses heap allocation → Kani struggles with `dealloc` analysis
//! - `RwLock` involves OS syscalls → Kani cannot model OS primitives
//! - Dynamic growth → unbounded state space for verification

use super::backend::ClockBackend;
use super::types::{LamportClock, ScheduledEvent, VirtualTimeNs};
use parking_lot::RwLock;
use std::collections::BinaryHeap;

/// Production-grade clock backend
///
/// # Thread Safety
/// Uses `RwLock` to allow:
/// - Multiple concurrent readers (`current_time()`, `is_empty()`)
/// - Exclusive writer for mutations (`push_event()`, `pop_event()`)
///
/// # Performance Characteristics
/// - Time complexity: O(log n) for push/pop
/// - Space complexity: O(n) dynamic allocation
/// - Lock contention: Read-optimized (most operations are reads)
pub struct ProductionBackend {
    /// Current virtual time (nanoseconds)
    /// Protected by inner RwLock in state
    state: RwLock<BackendState>,
}

struct BackendState {
    /// TLA+: virtualTimeNs
    virtual_time_ns: VirtualTimeNs,
    
    /// TLA+: lamportClock
    lamport_clock: LamportClock,
    
    /// TLA+: eventQueue
    /// Binary heap maintains min-heap property via ScheduledEvent's Ord impl
    event_queue: BinaryHeap<ScheduledEvent>,
}

impl ProductionBackend {
    /// Create new production backend
    pub fn new() -> Self {
        Self {
            state: RwLock::new(BackendState {
                virtual_time_ns: 0,
                lamport_clock: 0,
                event_queue: BinaryHeap::new(),
            }),
        }
    }
}

impl Default for ProductionBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl ClockBackend for ProductionBackend {
    fn current_time(&self) -> VirtualTimeNs {
        // Read lock: allows concurrent readers
        self.state.read().virtual_time_ns
    }

    fn current_lamport(&self) -> LamportClock {
        self.state.read().lamport_clock
    }

    fn set_time(&mut self, time: VirtualTimeNs) {
        // Write lock: exclusive access
        self.state.write().virtual_time_ns = time;
    }

    fn increment_lamport(&mut self) -> LamportClock {
        let mut state = self.state.write();
        state.lamport_clock += 1;
        state.lamport_clock
    }

    fn reset_lamport(&mut self) {
        self.state.write().lamport_clock = 0;
    }

    fn push_event(&mut self, event: ScheduledEvent) -> bool {
        // BinaryHeap automatically maintains heap property
        // ScheduledEvent's Ord implementation ensures correct ordering
        self.state.write().event_queue.push(event);
        true // Production backend has unbounded capacity
    }

    fn pop_event(&mut self) -> Option<ScheduledEvent> {
        // Pop returns highest priority (earliest time, lowest Lamport)
        self.state.write().event_queue.pop()
    }

    fn is_empty(&self) -> bool {
        self.state.read().event_queue.is_empty()
    }

    fn queue_len(&self) -> usize {
        self.state.read().event_queue.len()
    }

    fn reset(&mut self) {
        let mut state = self.state.write();
        state.virtual_time_ns = 0;
        state.lamport_clock = 0;
        state.event_queue.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::clock::types::EventPayload;

    #[test]
    fn test_production_backend_basic() {
        let mut backend = ProductionBackend::new();
        
        assert_eq!(backend.current_time(), 0);
        assert_eq!(backend.current_lamport(), 0);
        assert!(backend.is_empty());
        
        let event = ScheduledEvent::new(100, 1, 1, EventPayload::Test(0));
        assert!(backend.push_event(event));
        assert!(!backend.is_empty());
        assert_eq!(backend.queue_len(), 1);
    }

    #[test]
    fn test_production_backend_ordering() {
        let mut backend = ProductionBackend::new();
        
        // Insert in arbitrary order
        backend.push_event(ScheduledEvent::new(200, 2, 2, EventPayload::Test(0)));
        backend.push_event(ScheduledEvent::new(100, 1, 1, EventPayload::Test(0)));
        backend.push_event(ScheduledEvent::new(150, 3, 3, EventPayload::Test(0)));
        
        // Should pop in time order
        assert_eq!(backend.pop_event().unwrap().scheduled_at_ns, 100);
        assert_eq!(backend.pop_event().unwrap().scheduled_at_ns, 150);
        assert_eq!(backend.pop_event().unwrap().scheduled_at_ns, 200);
    }
}