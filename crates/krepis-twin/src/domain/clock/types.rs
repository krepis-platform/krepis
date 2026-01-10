//! Virtual Clock Types
//!
//! # TLA+ Correspondence
//! This module defines the Rust types that correspond to the TLA+ specification
//! in `specs/tla/VirtualClock.tla`.

use std::cmp::Ordering;

/// Virtual time in nanoseconds
///
/// # TLA+ Correspondence
/// Corresponds to `virtualTimeNs` variable in VirtualClock.tla
pub type VirtualTimeNs = u64;

/// Lamport logical clock value
///
/// # TLA+ Correspondence
/// Corresponds to `lamportClock` variable in VirtualClock.tla
pub type LamportClock = u64;

/// Unique event identifier
pub type EventId = u64;

/// Simulation mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeMode {
    /// Event-driven: Time advances only when events fire
    EventDriven,
    /// Real-time: Time advances continuously (for future use)
    RealTime,
}

/// Event payload types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EventPayload {
    /// Test event with arbitrary data
    Test(u64),
    /// Memory write synchronization
    MemoryWriteSync {
        /// Core performing the write
        core: usize,
        /// Target address
        addr: usize,
        /// Value to write
        value: u64,
    },
    /// Memory fence
    MemoryFence {
        /// Core issuing fence
        core: usize,
    },
    /// Scheduler task ready
    TaskReady {
        /// Task identifier
        task_id: String,
    },
    /// Watchdog timeout
    WatchdogTimeout {
        /// Tenant identifier
        tenant_id: String,
    },
    /// Custom event
    Custom(String),
}

/// Scheduled event in the event queue
///
/// # TLA+ Correspondence
/// Corresponds to elements in the `eventQueue` set in VirtualClock.tla
/// Each event has: [time |-> t, lamport |-> l]
#[derive(Debug, Clone)]
pub struct ScheduledEvent {
    /// When this event should fire (virtual time)
    pub scheduled_at_ns: VirtualTimeNs,
    
    /// Lamport clock value for causality tracking
    pub lamport: LamportClock,
    
    /// Unique event identifier
    pub event_id: EventId,
    
    /// Event payload
    pub payload: EventPayload,
}

impl ScheduledEvent {
    /// Create a new scheduled event
    pub fn new(
        scheduled_at_ns: VirtualTimeNs,
        lamport: LamportClock,
        event_id: EventId,
        payload: EventPayload,
    ) -> Self {
        Self {
            scheduled_at_ns,
            lamport,
            event_id,
            payload,
        }
    }
}

/// Event ordering for priority queue
///
/// # TLA+ Correspondence
/// Implements the `SelectNextEvent` logic from VirtualClock.tla:
/// ```tla
/// CHOOSE e \in eventQueue :
///     \A other \in eventQueue :
///         \/ e.time < other.time
///         \/ (e.time = other.time /\ e.lamport <= other.lamport)
/// ```
impl PartialEq for ScheduledEvent {
    fn eq(&self, other: &Self) -> bool {
        self.event_id == other.event_id
    }
}

impl Eq for ScheduledEvent {}

impl PartialOrd for ScheduledEvent {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ScheduledEvent {
    fn cmp(&self, other: &Self) -> Ordering {
        // Primary: Compare by scheduled time (earlier is greater for min-heap)
        match other.scheduled_at_ns.cmp(&self.scheduled_at_ns) {
            Ordering::Equal => {
                // Secondary: Compare by Lamport clock (smaller is greater for min-heap)
                match other.lamport.cmp(&self.lamport) {
                    Ordering::Equal => {
                        // Tertiary: Compare by event_id for determinism
                        other.event_id.cmp(&self.event_id)
                    }
                    ord => ord,
                }
            }
            ord => ord,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_event_ordering_by_time() {
        let e1 = ScheduledEvent::new(100, 1, 1, EventPayload::Test(0));
        let e2 = ScheduledEvent::new(200, 1, 2, EventPayload::Test(0));
        
        // Earlier time has higher priority
        assert!(e1 > e2);
    }

    #[test]
    fn test_event_ordering_by_lamport() {
        let e1 = ScheduledEvent::new(100, 1, 1, EventPayload::Test(0));
        let e2 = ScheduledEvent::new(100, 2, 2, EventPayload::Test(0));
        
        // Same time: smaller Lamport has higher priority
        assert!(e1 > e2);
    }

    #[test]
    fn test_event_ordering_deterministic() {
        let e1 = ScheduledEvent::new(100, 1, 1, EventPayload::Test(0));
        let e2 = ScheduledEvent::new(100, 1, 2, EventPayload::Test(0));
        
        // Same time and Lamport: smaller event_id has higher priority
        assert!(e1 > e2);
    }
}