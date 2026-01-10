//! Virtual Clock Engine - The Zero-cost Razor
//!
//! # Architecture Philosophy
//!
//! This module demonstrates **Zero-cost Abstraction** at its finest:
//! ```text
//! ┌─────────────────────────────────────────────────────────┐
//! │            VirtualClock<Backend>                        │
//! │            (Generic, Monomorphized)                     │
//! ├─────────────────────────────────────────────────────────┤
//! │  Compile Time         │   Runtime                       │
//! ├───────────────────────┼─────────────────────────────────┤
//! │  Production:          │  BinaryHeap + RwLock            │
//! │  VirtualClock<Prod>   │  (thread-safe, heap)            │
//! ├───────────────────────┼─────────────────────────────────┤
//! │  Verification:        │  [Option<Event>; 4] + RefCell   │
//! │  VirtualClock<Verify> │  (stack-only, Kani-friendly)    │
//! └─────────────────────────────────────────────────────────┘
//! ```
//!
//! The magic: **one generic function** becomes **two specialized functions**
//! at compile time, each optimized for its specific backend. No vtables,
//! no dynamic dispatch, no runtime overhead.

use super::backend::ClockBackend;
use super::types::{EventId, EventPayload, LamportClock, ScheduledEvent, TimeMode, VirtualTimeNs};
use std::cell::Cell;

/// Virtual clock with pluggable backend
///
/// # Type Parameter
/// - `B`: The backend implementation (Production or Verification)
///
/// # Monomorphization
/// When you write `VirtualClock<ProductionBackend>`, the Rust compiler generates
/// a completely separate version of this struct with all `B::method()` calls
/// inlined and specialized. It's as if you hand-wrote two separate implementations.
///
/// # TLA+ Correspondence
/// ```tla
/// VARIABLES virtualTimeNs, lamportClock, eventQueue
/// ```
pub struct VirtualClock<B: ClockBackend> {
    /// Pluggable backend (injected at construction)
    backend: B,
    
    /// Simulation mode (EventDriven vs RealTime)
    #[allow(dead_code)]
    mode: TimeMode,
    
    /// Next event ID allocator
    /// Uses Cell for interior mutability (no locks needed)
    next_event_id: Cell<EventId>,
    
    /// Maximum virtual time (for bounded model checking)
    max_time_ns: VirtualTimeNs,
    
    /// Maximum event queue size (for bounded model checking)
    max_events: usize,
}

impl<B: ClockBackend> VirtualClock<B> {
    /// Create new virtual clock with custom backend
    ///
    /// # Type Inference
    /// ```rust
    /// use krepis_twin::domain::clock::{VirtualClock, ProductionBackend, TimeMode};
    ///
    /// let backend = ProductionBackend::new();
    /// let clock = VirtualClock::new(backend, TimeMode::EventDriven);
    /// ```
    pub fn new(backend: B, mode: TimeMode) -> Self {
        Self::with_limits(backend, mode, u64::MAX, usize::MAX)
    }

    /// Create clock with bounded limits (for verification)
    pub fn with_limits(
        backend: B,
        mode: TimeMode,
        max_time_ns: VirtualTimeNs,
        max_events: usize,
    ) -> Self {
        Self {
            backend,
            mode,
            next_event_id: Cell::new(0),
            max_time_ns,
            max_events,
        }
    }

    /// Get current virtual time
    ///
    /// # Inlining
    /// In production: inlines to `self.backend.state.read().virtual_time_ns`
    /// In verification: inlines to `self.backend.state.borrow().virtual_time_ns`
    pub fn now_ns(&self) -> VirtualTimeNs {
        self.backend.current_time()
    }

    /// Get current Lamport clock
    pub fn lamport(&self) -> LamportClock {
        self.backend.current_lamport()
    }

    /// Get pending events count
    pub fn pending_events(&self) -> usize {
        self.backend.queue_len()
    }

    /// Schedule a future event
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// ScheduleEvent(delay) ==
    ///     /\ virtualTimeNs + delay <= MaxTimeNs
    ///     /\ Cardinality(eventQueue) < MaxEvents
    ///     /\ LET newLamport == lamportClock + 1
    ///        IN  /\ eventQueue' = eventQueue \cup {CreateEvent(...)}
    ///            /\ lamportClock' = newLamport
    /// ```
    pub fn schedule(&mut self, delay_ns: VirtualTimeNs, payload: EventPayload) -> Option<EventId> {
        let current_time = self.backend.current_time();
        
        // Precondition: check time bounds
        let scheduled_at_ns = current_time.checked_add(delay_ns)?;
        if scheduled_at_ns > self.max_time_ns {
            return None;
        }
        
        // Precondition: check queue capacity
        if self.backend.queue_len() >= self.max_events {
            return None;
        }
        
        // TLA+: lamportClock' = lamportClock + 1
        let lamport = self.backend.increment_lamport();
        
        // Allocate event ID
        let event_id = self.next_event_id.get();
        self.next_event_id.set(event_id + 1);
        
        // TLA+: eventQueue' = eventQueue \cup {newEvent}
        let event = ScheduledEvent::new(scheduled_at_ns, lamport, event_id, payload);
        if self.backend.push_event(event) {
            Some(event_id)
        } else {
            None
        }
    }

    /// Process next event (advance time)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Tick ==
    ///     /\ eventQueue /= {}
    ///     /\ LET nextEvent == CHOOSE e \in eventQueue : (...)
    ///        IN  /\ virtualTimeNs' = nextEvent.time
    ///            /\ eventQueue' = eventQueue \ {nextEvent}
    ///            /\ lamportClock' = IF eventQueue' = {} THEN 0 ELSE lamportClock
    /// ```
    pub fn tick(&mut self) -> Option<ScheduledEvent> {
        // TLA+: eventQueue /= {}
        let event = self.backend.pop_event()?;
        
        // TLA+: virtualTimeNs' = nextEvent.time
        // Invariant T-001: Time monotonicity
        assert!(
            event.scheduled_at_ns >= self.backend.current_time(),
            "Time monotonicity violated: {} < {}",
            event.scheduled_at_ns,
            self.backend.current_time()
        );
        self.backend.set_time(event.scheduled_at_ns);
        
        // TLA+: lamportClock' = IF eventQueue' = {} THEN 0 ELSE lamportClock
        if self.backend.is_empty() {
            self.backend.reset_lamport();
        }
        
        Some(event)
    }

    /// Check if idle
    pub fn is_idle(&self) -> bool {
        self.backend.is_empty()
    }

    /// Reset to initial state
    pub fn reset(&mut self) {
        self.backend.reset();
        self.next_event_id.set(0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::clock::production_backend::ProductionBackend;
    use crate::domain::clock::verification_backend::VerificationBackend;

    #[test]
    fn test_generic_clock_production() {
        let backend = ProductionBackend::new();
        let mut clock = VirtualClock::new(backend, TimeMode::EventDriven);
        
        clock.schedule(100, EventPayload::Test(1)).unwrap();
        clock.schedule(50, EventPayload::Test(2)).unwrap();
        
        let mut prev_time = 0;
        while let Some(event) = clock.tick() {
            assert!(event.scheduled_at_ns >= prev_time);
            prev_time = event.scheduled_at_ns;
        }
    }

    #[test]
    fn test_generic_clock_verification() {
        let backend = VerificationBackend::new();
        let mut clock = VirtualClock::new(backend, TimeMode::EventDriven);
        
        clock.schedule(100, EventPayload::Test(1)).unwrap();
        clock.schedule(50, EventPayload::Test(2)).unwrap();
        
        let mut prev_time = 0;
        while let Some(event) = clock.tick() {
            assert!(event.scheduled_at_ns >= prev_time);
            prev_time = event.scheduled_at_ns;
        }
    }

    #[test]
    fn test_zero_cost_abstraction() {
        // Both backends have identical interface
        // but compile to completely different machine code
        
        let backend_p = ProductionBackend::new();
        let mut clock_p = VirtualClock::new(backend_p, TimeMode::EventDriven);
        
        let backend_v = VerificationBackend::new();
        let mut clock_v = VirtualClock::new(backend_v, TimeMode::EventDriven);
        
        // Same code, different implementations
        clock_p.schedule(100, EventPayload::Test(0)).unwrap();
        clock_v.schedule(100, EventPayload::Test(0)).unwrap();
        
        assert_eq!(clock_p.tick().unwrap().scheduled_at_ns, 100);
        assert_eq!(clock_v.tick().unwrap().scheduled_at_ns, 100);
    }
}