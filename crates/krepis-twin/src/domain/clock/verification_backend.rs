//! Verification Backend Implementation
//!
//! # The Kani Whisperer
//!
//! This backend is specifically designed to make Kani happy by eliminating
//! everything it struggles with:
//! - ❌ No heap allocation → ✅ Fixed-size stack arrays
//! - ❌ No OS syscalls → ✅ RefCell for interior mutability
//! - ❌ No unbounded loops → ✅ Bounded iteration with const generics
//!
//! # Design Rationale
//!
//! Kani uses symbolic execution to explore all possible program states.
//! Heap allocation creates infinite state spaces (malloc can fail, pointers
//! can be anywhere). By using fixed-size arrays, we give Kani a **finite,
//! bounded state space** it can exhaustively verify.
//!
//! # Performance Trade-offs
//!
//! In verification mode, we accept:
//! - Limited capacity (MAX_EVENTS)
//! - O(n) insertion/deletion (linear scan)
//! - Single-threaded only (RefCell)
//!
//! These trade-offs are acceptable because verification runs on **small,
//! bounded test cases**, not production workloads.

use super::backend::ClockBackend;
use super::types::{LamportClock, ScheduledEvent, VirtualTimeNs};
use std::cell::RefCell;

/// Maximum events for verification (must be small for Kani)
///
/// Why 4? Kani's state space grows exponentially with array size.
/// With 4 slots, we can verify all possible orderings while keeping
/// verification time under 60 seconds.
const MAX_EVENTS: usize = 4;

/// Verification-friendly clock backend
///
/// # Memory Layout
/// ```text
/// ┌─────────────────────────────────────────────┐
/// │ VerificationBackend                         │
/// ├─────────────────────────────────────────────┤
/// │ state: RefCell<BackendState>                │
/// │   ├─ virtual_time_ns: u64                   │
/// │   ├─ lamport_clock: u64                     │
/// │   ├─ event_count: usize                     │
/// │   └─ events: [Option<ScheduledEvent>; 4]    │
/// │       ├─ [0]: Some(Event)  ← Stack memory   │
/// │       ├─ [1]: None                          │
/// │       ├─ [2]: Some(Event)                   │
/// │       └─ [3]: None                          │
/// └─────────────────────────────────────────────┘
/// ```
///
/// Everything lives on the stack. Kani can see the entire memory layout
/// at compile time, making verification tractable.
pub struct VerificationBackend {
    state: RefCell<BackendState>,
}

struct BackendState {
    /// TLA+: virtualTimeNs
    virtual_time_ns: VirtualTimeNs,
    
    /// TLA+: lamportClock
    lamport_clock: LamportClock,
    
    /// Number of events currently in queue
    event_count: usize,
    
    /// TLA+: eventQueue
    /// Fixed-size array on the stack. Each slot is Option<Event>:
    /// - Some(event) → slot is occupied
    /// - None → slot is free
    ///
    /// We maintain a "sparse array" where events can be in any position.
    /// This avoids the need for complex data structure rebalancing.
    events: [Option<ScheduledEvent>; MAX_EVENTS],
}

impl VerificationBackend {
    /// Create new verification backend
    pub fn new() -> Self {
        Self {
            state: RefCell::new(BackendState {
                virtual_time_ns: 0,
                lamport_clock: 0,
                event_count: 0,
                events: [None, None, None, None],
            }),
        }
    }

    /// Find index of next event to fire
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// CHOOSE e \in eventQueue :
    ///     \A other \in eventQueue :
    ///         \/ e.time < other.time
    ///         \/ (e.time = other.time /\ e.lamport <= other.lamport)
    /// ```
    ///
    /// # Algorithm
    /// Linear scan through array to find event with:
    /// 1. Earliest scheduled_at_ns
    /// 2. If tied, lowest lamport
    /// 3. If still tied, lowest event_id (for determinism)
    fn find_next_event_index(events: &[Option<ScheduledEvent>; MAX_EVENTS]) -> Option<usize> {
        let mut best_idx: Option<usize> = None;
        
        for (i, slot) in events.iter().enumerate() {
            if let Some(event) = slot {
                // Update best if:
                // 1. No candidate yet, OR
                // 2. This event comes before current best
                best_idx = match best_idx {
                    None => Some(i),
                    Some(current_best) => {
                        let current_event = events[current_best].as_ref().unwrap();
                        
                        // Use ScheduledEvent's Ord implementation
                        // (lower values = higher priority in our ordering)
                        if event > current_event {
                            Some(i)
                        } else {
                            Some(current_best)
                        }
                    }
                };
            }
        }
        
        best_idx
    }
}

impl Default for VerificationBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl ClockBackend for VerificationBackend {
    fn current_time(&self) -> VirtualTimeNs {
        self.state.borrow().virtual_time_ns
    }

    fn current_lamport(&self) -> LamportClock {
        self.state.borrow().lamport_clock
    }

    fn set_time(&mut self, time: VirtualTimeNs) {
        self.state.borrow_mut().virtual_time_ns = time;
    }

    fn increment_lamport(&mut self) -> LamportClock {
        let mut state = self.state.borrow_mut();
        state.lamport_clock += 1;
        state.lamport_clock
    }

    fn reset_lamport(&mut self) {
        self.state.borrow_mut().lamport_clock = 0;
    }

    fn push_event(&mut self, event: ScheduledEvent) -> bool {
        let mut state = self.state.borrow_mut();
        
        // Check capacity (bounded verification)
        if state.event_count >= MAX_EVENTS {
            return false; // Queue full
        }
        
        // Find first empty slot (linear scan is OK for small arrays)
        for slot in &mut state.events {
            if slot.is_none() {
                *slot = Some(event);
                state.event_count += 1;
                return true;
            }
        }
        
        // Should never reach here if event_count is accurate
        false
    }

    fn pop_event(&mut self) -> Option<ScheduledEvent> {
        let mut state = self.state.borrow_mut();
        
        if state.event_count == 0 {
            return None;
        }
        
        // Find next event to fire
        let next_idx = Self::find_next_event_index(&state.events)?;
        
        // Take event (replaces with None)
        let event = state.events[next_idx].take();
        state.event_count -= 1;
        
        event
    }

    fn is_empty(&self) -> bool {
        self.state.borrow().event_count == 0
    }

    fn queue_len(&self) -> usize {
        self.state.borrow().event_count
    }

    fn reset(&mut self) {
        let mut state = self.state.borrow_mut();
        state.virtual_time_ns = 0;
        state.lamport_clock = 0;
        state.event_count = 0;
        state.events = [None, None, None, None];
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::clock::types::EventPayload;

    #[test]
    fn test_verification_backend_basic() {
        let mut backend = VerificationBackend::new();
        
        assert_eq!(backend.current_time(), 0);
        assert_eq!(backend.current_lamport(), 0);
        assert!(backend.is_empty());
        
        let event = ScheduledEvent::new(100, 1, 1, EventPayload::Test(0));
        assert!(backend.push_event(event));
        assert!(!backend.is_empty());
        assert_eq!(backend.queue_len(), 1);
    }

    #[test]
    fn test_verification_backend_ordering() {
        let mut backend = VerificationBackend::new();
        
        // Insert in arbitrary order
        backend.push_event(ScheduledEvent::new(200, 2, 2, EventPayload::Test(0)));
        backend.push_event(ScheduledEvent::new(100, 1, 1, EventPayload::Test(0)));
        backend.push_event(ScheduledEvent::new(150, 3, 3, EventPayload::Test(0)));
        
        // Should pop in time order
        assert_eq!(backend.pop_event().unwrap().scheduled_at_ns, 100);
        assert_eq!(backend.pop_event().unwrap().scheduled_at_ns, 150);
        assert_eq!(backend.pop_event().unwrap().scheduled_at_ns, 200);
    }

    #[test]
    fn test_verification_backend_capacity() {
        let mut backend = VerificationBackend::new();
        
        // Fill to capacity
        for i in 0..MAX_EVENTS {
            let event = ScheduledEvent::new(i as u64 * 100, i as u64, i as u64, EventPayload::Test(0));
            assert!(backend.push_event(event));
        }
        
        // Should reject when full
        let overflow = ScheduledEvent::new(999, 999, 999, EventPayload::Test(0));
        assert!(!backend.push_event(overflow));
    }
}