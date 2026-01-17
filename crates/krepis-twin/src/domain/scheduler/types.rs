//! Scheduler Types - Foundation for SchedulerOracle
//!
//! # TLA+ Correspondence
//!
//! This module defines the Rust types that correspond to the TLA+ specification
//! in `specs/tla/SchedulerOracle.tla`. Each type here maps directly to a TLA+
//! constant, variable, or type definition.
//!
//! # Design Philosophy
//!
//! These types are designed to be:
//! - **Zero-cost**: All types compile to efficient machine code with no runtime overhead
//! - **Type-safe**: The type system prevents invalid states at compile time
//! - **Verifiable**: Compatible with Kani formal verification
//! - **Explicit**: No hidden state or implicit behavior
//!
//! # TLA+ Mapping
//!
//! ```tla
//! CONSTANTS Strategy
//! VARIABLES threadStates
//! ThreadStates == {"RUNNABLE", "BLOCKED", "COMPLETED"}
//! ```

use std::fmt;

/// Thread identifier
///
/// # TLA+ Correspondence
/// ```tla
/// CONSTANTS Threads
/// Threads = {t1, t2, t3, ...}
/// ```
///
/// # Design Notes
///
/// We use a newtype pattern here rather than a raw usize for several important reasons.
/// First, it provides type safety - you cannot accidentally use a random number where
/// a ThreadId is expected. Second, it makes the code self-documenting - when you see
/// ThreadId in a function signature, you immediately understand what kind of value is
/// expected. Third, it allows us to add validation logic if needed in the future.
///
/// The inner usize is public for now to allow easy construction and access, but we
/// could make it private later if we need to add invariants.
///
/// # Example
///
/// ```rust
/// use krepis_twin::domain::scheduler::ThreadId;
///
/// let thread_1 = ThreadId::new(0);
/// let thread_2 = ThreadId::new(1);
///
/// assert_ne!(thread_1, thread_2);
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ThreadId(pub usize);

impl ThreadId {
    /// Create a new ThreadId
    ///
    /// # Arguments
    /// - `id`: The numeric identifier for this thread
    ///
    /// # Design Note
    ///
    /// We do not validate the ID here because validation depends on the backend
    /// configuration. The ProductionBackend might support millions of threads,
    /// while VerificationBackend might only support 4 threads. The backend is
    /// responsible for checking bounds when a ThreadId is used.
    #[inline(always)]
    pub const fn new(id: usize) -> Self {
        Self(id)
    }

    /// Get the raw numeric ID
    #[inline(always)]
    pub const fn as_usize(self) -> usize {
        self.0
    }
}

impl fmt::Display for ThreadId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Thread({})", self.0)
    }
}

/// Task identifier
///
/// # TLA+ Correspondence
/// ```tla
/// Each event in eventQueue has an eventId field
/// ```
///
/// # Design Notes
///
/// TaskId and EventId serve different conceptual purposes even though they might
/// have similar internal representations. An EventId identifies a specific scheduled
/// event in the clock's event queue. A TaskId identifies a logical unit of work that
/// might spawn multiple events.
///
/// For Phase 1A, we use TaskId primarily for associating events with threads. In
/// Phase 1B when we add dependencies, TaskId will become more important - we will
/// track which tasks depend on which other tasks.
///
/// Like ThreadId, this is a newtype for type safety and clarity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TaskId(pub usize);

impl TaskId {
    /// Create a new TaskId
    #[inline(always)]
    pub const fn new(id: usize) -> Self {
        Self(id)
    }

    /// Get the raw numeric ID
    #[inline(always)]
    pub const fn as_usize(self) -> usize {
        self.0
    }
}

impl fmt::Display for TaskId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Task({})", self.0)
    }
}

/// Thread state in the scheduler
///
/// # TLA+ Correspondence
/// ```tla
/// ThreadStates == {"RUNNABLE", "BLOCKED", "COMPLETED"}
/// ```
///
/// # State Transitions
///
/// The valid state transitions are:
/// ```text
/// RUNNABLE ──────> BLOCKED      (thread waits for resource)
///    ↑                │
///    └────────────────┘          (resource becomes available)
///
/// RUNNABLE ──────> COMPLETED    (thread finishes execution)
/// ```
///
/// # Design Notes
///
/// In Phase 1A, we primarily use RUNNABLE and COMPLETED. The BLOCKED state exists
/// in the type system but is not heavily used yet. In Phase 1B when we add resource
/// contention and dependencies, BLOCKED becomes critical.
///
/// A thread in RUNNABLE state can have its events scheduled and executed. A thread
/// in BLOCKED state has events in the queue but they should not be executed until
/// the thread becomes RUNNABLE again. A thread in COMPLETED state should have no
/// events and should not be scheduled.
///
/// This enum derives Copy because it is small (single byte) and copyable semantics
/// are more ergonomic than move semantics for state values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ThreadState {
    /// Thread is ready to run
    ///
    /// Events belonging to this thread can be executed when they reach the front
    /// of the event queue (according to time and Lamport ordering).
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// threadStates[t] = "RUNNABLE"
    /// ```
    Runnable,

    /// Thread is waiting for a resource or dependency
    ///
    /// Events belonging to this thread should not be executed even if they are
    /// at the front of the queue. The thread must transition back to RUNNABLE
    /// before its events can execute.
    ///
    /// # Phase 1B Extension
    ///
    /// In Phase 1B, we will add fields to track what the thread is blocked on:
    /// - Resource ID (mutex, semaphore, etc.)
    /// - Dependency (waiting for another task to complete)
    ///
    /// For now, BLOCKED is a simple marker with no associated data.
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// threadStates[t] = "BLOCKED"
    /// ```
    Blocked,

    /// Thread has finished execution
    ///
    /// This thread should have no pending events and should not schedule new events.
    /// This is a terminal state - once a thread is COMPLETED, it stays COMPLETED.
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// threadStates[t] = "COMPLETED"
    /// ```
    Completed,
}

impl ThreadState {
    /// Check if thread can execute events
    ///
    /// # Returns
    ///
    /// `true` if the thread is in RUNNABLE state, `false` otherwise.
    ///
    /// # Usage in SchedulerOracle
    ///
    /// When selecting the next event to execute, we filter the event queue to only
    /// include events from threads where `is_runnable()` returns true. This implements
    /// the TLA+ specification's `RunnableEvents` definition:
    ///
    /// ```tla
    /// RunnableEvents == {e \in eventQueue : threadStates[e.thread] = "RUNNABLE"}
    /// ```
    #[inline(always)]
    pub const fn is_runnable(self) -> bool {
        matches!(self, ThreadState::Runnable)
    }

    /// Check if thread is blocked
    #[inline(always)]
    pub const fn is_blocked(self) -> bool {
        matches!(self, ThreadState::Blocked)
    }

    /// Check if thread is completed
    #[inline(always)]
    pub const fn is_completed(self) -> bool {
        matches!(self, ThreadState::Completed)
    }
}

impl fmt::Display for ThreadState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThreadState::Runnable => write!(f, "RUNNABLE"),
            ThreadState::Blocked => write!(f, "BLOCKED"),
            ThreadState::Completed => write!(f, "COMPLETED"),
        }
    }
}

/// Scheduling strategy
///
/// # TLA+ Correspondence
/// ```tla
/// CONSTANTS Strategy
/// ASSUME Strategy \in {"PRODUCTION", "VERIFICATION"}
/// ```
///
/// # Design Notes
///
/// The scheduling strategy determines how the SchedulerOracle selects which event
/// to execute next when multiple events are runnable at the same time.
///
/// In PRODUCTION mode, the selection is deterministic. Given the same set of events,
/// we always choose the same one. This makes the simulation reproducible and debuggable.
/// We use a total ordering based on (time, lamport, event_id) to achieve determinism.
///
/// In VERIFICATION mode, the selection can be non-deterministic. This allows tools
/// like TLC model checker or Kani to explore all possible interleavings. By trying
/// every possible execution order, we can find concurrency bugs that only manifest
/// in specific thread interleavings.
///
/// # Why This Matters
///
/// Consider two events that happen at the same virtual time with the same Lamport
/// clock value (this can happen if they are on different threads and there has been
/// no communication between them). In PRODUCTION mode, we break the tie using event_id,
/// so we always execute them in the same order. In VERIFICATION mode, we might try
/// both orders to see if either one violates an invariant.
///
/// This is the essence of formal verification: exhaustively exploring possibilities
/// that real execution would only visit randomly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchedulingStrategy {
    /// Deterministic scheduling for production use
    ///
    /// When multiple events are runnable at the same time, always select the
    /// same one based on a total ordering (time, lamport, event_id).
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// ExecuteNext_Production ==
    ///     /\ Strategy = "PRODUCTION"
    ///     /\ LET nextEvent == CHOOSE e \in RunnableEvents : (...)
    ///        IN (...)
    /// ```
    Production,

    /// Non-deterministic scheduling for verification
    ///
    /// When multiple events are runnable at the same time, the verifier can
    /// explore different execution orders.
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// ExecuteNext_Verification ==
    ///     /\ Strategy = "VERIFICATION"
    ///     /\ \E nextEvent \in RunnableEvents : (...)
    /// ```
    Verification,
}

impl SchedulingStrategy {
    /// Check if using production strategy
    #[inline(always)]
    pub const fn is_production(self) -> bool {
        matches!(self, SchedulingStrategy::Production)
    }

    /// Check if using verification strategy
    #[inline(always)]
    pub const fn is_verification(self) -> bool {
        matches!(self, SchedulingStrategy::Verification)
    }
}

impl fmt::Display for SchedulingStrategy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SchedulingStrategy::Production => write!(f, "PRODUCTION"),
            SchedulingStrategy::Verification => write!(f, "VERIFICATION"),
        }
    }
}

/// Error type for scheduler operations
///
/// # Design Notes
///
/// This enum captures all the ways that scheduler operations can fail. Each variant
/// corresponds to a precondition violation in the TLA+ specification.
///
/// For example, the TLA+ specification says:
/// ```tla
/// ScheduleEvent(thread, delay) ==
///     /\ virtualTimeNs + delay <= MaxTimeNs
///     /\ Cardinality(eventQueue) < MaxEvents
///     /\ thread \in Threads
/// ```
///
/// If any of these preconditions is violated, we return an appropriate error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchedulerError {
    /// Thread ID is invalid (out of bounds for the backend)
    ///
    /// This error occurs when you try to schedule a task for a thread that does
    /// not exist in the backend's thread state table.
    InvalidThreadId {
        thread_id: ThreadId,
        max_threads: usize,
    },

    /// Thread is not in a valid state for the requested operation
    ///
    /// For example, trying to schedule an event for a COMPLETED thread, or trying
    /// to execute an event from a BLOCKED thread.
    InvalidThreadState {
        thread_id: ThreadId,
        current_state: ThreadState,
        expected_state: ThreadState,
    },

    /// Event queue is full (hit MaxEvents limit)
    ///
    /// This is primarily a concern in VerificationBackend where we have strict
    /// bounds for model checking. In ProductionBackend, the queue can grow very
    /// large before hitting this error.
    QueueFull {
        max_events: usize,
    },

    /// Virtual time overflow (would exceed MaxTimeNs)
    ///
    /// This happens if you try to schedule an event so far in the future that
    /// it would overflow the time representation or exceed configured limits.
    TimeOverflow {
        current_time_ns: u64,
        delay_ns: u64,
        max_time_ns: u64,
    },

    /// No runnable events available
    ///
    /// This is not necessarily an error condition - it just means the scheduler
    /// is idle. All events are either completed or blocked.
    NoRunnableEvents,
}

impl fmt::Display for SchedulerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SchedulerError::InvalidThreadId { thread_id, max_threads } => {
                write!(
                    f,
                    "Invalid thread ID: {} (max threads: {})",
                    thread_id, max_threads
                )
            }
            SchedulerError::InvalidThreadState {
                thread_id,
                current_state,
                expected_state,
            } => {
                write!(
                    f,
                    "Thread {} in invalid state: {} (expected: {})",
                    thread_id, current_state, expected_state
                )
            }
            SchedulerError::QueueFull { max_events } => {
                write!(f, "Event queue full (max events: {})", max_events)
            }
            SchedulerError::TimeOverflow {
                current_time_ns,
                delay_ns,
                max_time_ns,
            } => {
                write!(
                    f,
                    "Time overflow: {} + {} would exceed max time {}",
                    current_time_ns, delay_ns, max_time_ns
                )
            }
            SchedulerError::NoRunnableEvents => {
                write!(f, "No runnable events available")
            }
        }
    }
}

impl std::error::Error for SchedulerError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_id_creation() {
        let tid = ThreadId::new(42);
        assert_eq!(tid.as_usize(), 42);
        assert_eq!(format!("{}", tid), "Thread(42)");
    }

    #[test]
    fn test_thread_state_predicates() {
        assert!(ThreadState::Runnable.is_runnable());
        assert!(!ThreadState::Runnable.is_blocked());
        assert!(!ThreadState::Runnable.is_completed());

        assert!(!ThreadState::Blocked.is_runnable());
        assert!(ThreadState::Blocked.is_blocked());
        assert!(!ThreadState::Blocked.is_completed());

        assert!(!ThreadState::Completed.is_runnable());
        assert!(!ThreadState::Completed.is_blocked());
        assert!(ThreadState::Completed.is_completed());
    }

    #[test]
    fn test_scheduling_strategy_predicates() {
        assert!(SchedulingStrategy::Production.is_production());
        assert!(!SchedulingStrategy::Production.is_verification());

        assert!(!SchedulingStrategy::Verification.is_production());
        assert!(SchedulingStrategy::Verification.is_verification());
    }

    #[test]
    fn test_error_display() {
        let err = SchedulerError::InvalidThreadId {
            thread_id: ThreadId::new(5),
            max_threads: 4,
        };
        let msg = format!("{}", err);
        assert!(msg.contains("Invalid thread ID"));
        assert!(msg.contains("5"));
        assert!(msg.contains("4"));
    }
}