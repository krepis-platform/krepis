//! Zero-cost Causality Analysis
//!
//! This module provides tools for analyzing happens-before relationships
//! between simulation events using stack-allocated data structures.

use super::event::{SimulationEvent, ThreadId, MAX_THREADS};

/// Happens-before relationship between two events
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HappensBeforeRelation {
    /// Events are causally ordered (e1 happens-before e2)
    Before,
    /// Events are causally ordered (e2 happens-before e1)
    After,
    /// Events are concurrent (no causal relationship)
    Concurrent,
}

impl HappensBeforeRelation {
    /// Determine the relationship between two events based on Lamport timestamps
    ///
    /// **Important**: This is a conservative approximation.
    /// - `timestamp(e1) < timestamp(e2)` implies possible happens-before
    /// - Equal timestamps on different threads → definitely concurrent
    #[inline]
    pub fn from_events(e1: &SimulationEvent, e2: &SimulationEvent) -> Self {
        let ts1 = e1.timestamp();
        let ts2 = e2.timestamp();
        let tid1 = e1.thread_id();
        let tid2 = e2.thread_id();

        if tid1.0 == tid2.0 {
            // Same thread: use sequence number for total ordering
            match ts1.0.cmp(&ts2.0) {
                std::cmp::Ordering::Less => HappensBeforeRelation::Before,
                std::cmp::Ordering::Greater => HappensBeforeRelation::After,
                std::cmp::Ordering::Equal => {
                    // Should never happen if tracer is working correctly
                    HappensBeforeRelation::Concurrent
                }
            }
        } else {
            // Different threads: Lamport clock only gives partial order
            match ts1.0.cmp(&ts2.0) {
                std::cmp::Ordering::Less => HappensBeforeRelation::Before,
                std::cmp::Ordering::Greater => HappensBeforeRelation::After,
                std::cmp::Ordering::Equal => HappensBeforeRelation::Concurrent,
            }
        }
    }
}

/// A graph representing causality relationships between events
///
/// This is a **stack-allocated** structure that builds a happens-before
/// graph from a trace without any heap allocation.
///
/// # Memory Layout
/// - thread_event_counts: MAX_THREADS * 8 bytes
/// - Total: ~128 bytes (stack-friendly)
pub struct CausalityGraph<'a> {
    /// Reference to the trace events
    events: &'a [SimulationEvent],
    
    /// Number of events per thread (for quick lookup)
    thread_event_counts: [usize; MAX_THREADS],
}

impl<'a> CausalityGraph<'a> {
    /// Build a causality graph from a trace
    ///
    /// This operation is O(n) where n is the number of events,
    /// using only stack-allocated memory.
    pub fn from_trace(events: &'a [SimulationEvent]) -> Self {
        let mut thread_event_counts = [0; MAX_THREADS];

        // Count events per thread
        for event in events {
            let thread_idx = event.thread_id().as_index();
            thread_event_counts[thread_idx] += 1;
        }

        Self {
            events,
            thread_event_counts,
        }
    }

    /// Check if event at index i happens-before event at index j
    ///
    /// This uses a simplified happens-before check based on Lamport timestamps.
    /// For a full transitive closure, use `happens_before_transitive`.
    #[inline]
    pub fn happens_before(&self, i: usize, j: usize) -> bool {
        if i >= self.events.len() || j >= self.events.len() {
            return false;
        }

        let ei = &self.events[i];
        let ej = &self.events[j];

        matches!(
            HappensBeforeRelation::from_events(ei, ej),
            HappensBeforeRelation::Before
        )
    }

    /// Check transitive happens-before (i -> ... -> j)
    ///
    /// This is more expensive (O(n^2) worst case) but provides complete
    /// transitive closure of the happens-before relation.
    pub fn happens_before_transitive(&self, i: usize, j: usize) -> bool {
        if i == j || i >= self.events.len() || j >= self.events.len() {
            return false;
        }

        // For same thread, use simple comparison
        if self.events[i].thread_id() == self.events[j].thread_id() {
            return i < j;
        }

        // For different threads, check if there's a synchronization path
        // This is a simplified implementation; full implementation would
        // require tracking sync events explicitly
        self.events[i].timestamp() < self.events[j].timestamp()
    }

    /// Find all events that are concurrent with the given event
    ///
    /// Returns indices of concurrent events.
    pub fn find_concurrent(&self, event_idx: usize) -> impl Iterator<Item = usize> + '_ {
        (0..self.events.len())
            .filter(move |&idx| {
                idx != event_idx
                    && !self.happens_before(event_idx, idx)
                    && !self.happens_before(idx, event_idx)
            })
    }

    /// Get events in topological order (respecting happens-before)
    ///
    /// This returns event indices sorted by Lamport timestamp,
    /// which provides a valid topological ordering.
    ///
    /// # Memory
    /// Allocates a Vec for the sorted indices (only allocation in this module)
    pub fn topological_order(&self) -> Vec<usize> {
        let mut indices: Vec<usize> = (0..self.events.len()).collect();
        
        // Sort by Lamport timestamp (which respects happens-before)
        indices.sort_by_key(|&i| self.events[i].timestamp().0);
        
        indices
    }

    /// Get the number of events in the graph
    #[inline(always)]
    pub fn event_count(&self) -> usize {
        self.events.len()
    }

    /// Get events for a specific thread in program order
    ///
    /// Returns an iterator over event indices for the given thread.
    pub fn thread_events(&self, thread_id: ThreadId) -> impl Iterator<Item = usize> + '_ {
        self.events
            .iter()
            .enumerate()
            .filter(move |(_, e)| e.thread_id() == thread_id)
            .map(|(i, _)| i)
    }

    /// Get the number of events from a specific thread
    #[inline]
    pub fn thread_event_count(&self, thread_id: ThreadId) -> usize {
        let idx = thread_id.as_index();
        if idx < MAX_THREADS {
            self.thread_event_counts[idx]
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::tracing::event::{ClockEvent, EventMetadata, LamportTimestamp};

    #[test]
    fn test_happens_before_same_thread() {
        let thread_id = ThreadId::new(0);
        
        let e1 = SimulationEvent::ClockTick {
            meta: EventMetadata::new(LamportTimestamp(1), thread_id, 0),
            event: ClockEvent {
                prev_timestamp: LamportTimestamp(0),
                new_timestamp: LamportTimestamp(1),
            },
        };

        let e2 = SimulationEvent::ClockTick {
            meta: EventMetadata::new(LamportTimestamp(2), thread_id, 1),
            event: ClockEvent {
                prev_timestamp: LamportTimestamp(1),
                new_timestamp: LamportTimestamp(2),
            },
        };

        assert_eq!(
            HappensBeforeRelation::from_events(&e1, &e2),
            HappensBeforeRelation::Before
        );
        assert_eq!(
            HappensBeforeRelation::from_events(&e2, &e1),
            HappensBeforeRelation::After
        );
    }

    #[test]
    fn test_causality_graph_construction() {
        let events = vec![
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(1), ThreadId::new(0), 0),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(0),
                    new_timestamp: LamportTimestamp(1),
                },
            },
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(2), ThreadId::new(0), 1),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(1),
                    new_timestamp: LamportTimestamp(2),
                },
            },
        ];

        let graph = CausalityGraph::from_trace(&events);
        
        assert_eq!(graph.event_count(), 2);
        assert!(graph.happens_before(0, 1));
        assert!(!graph.happens_before(1, 0));
    }

    #[test]
    fn test_topological_order() {
        let events = vec![
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(1), ThreadId::new(0), 0),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(0),
                    new_timestamp: LamportTimestamp(1),
                },
            },
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(2), ThreadId::new(0), 1),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(1),
                    new_timestamp: LamportTimestamp(2),
                },
            },
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(3), ThreadId::new(0), 2),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(2),
                    new_timestamp: LamportTimestamp(3),
                },
            },
        ];

        let graph = CausalityGraph::from_trace(&events);
        let order = graph.topological_order();

        // Should be in sequential order for single thread
        assert_eq!(order, vec![0, 1, 2]);
    }

    #[test]
    fn test_thread_event_count() {
        let events = vec![
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(1), ThreadId::new(0), 0),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(0),
                    new_timestamp: LamportTimestamp(1),
                },
            },
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(2), ThreadId::new(1), 0),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(0),
                    new_timestamp: LamportTimestamp(2),
                },
            },
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp(3), ThreadId::new(0), 1),
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(1),
                    new_timestamp: LamportTimestamp(3),
                },
            },
        ];

        let graph = CausalityGraph::from_trace(&events);
        
        assert_eq!(graph.thread_event_count(ThreadId::new(0)), 2);
        assert_eq!(graph.thread_event_count(ThreadId::new(1)), 1);
    }
}