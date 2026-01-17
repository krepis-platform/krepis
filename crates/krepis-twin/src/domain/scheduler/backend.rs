//! Scheduler Backend Abstraction
//!
//! # Design Philosophy
//!
//! This module defines the `SchedulerBackend` trait, which abstracts over different
//! implementations of thread state management. The trait allows us to have one
//! SchedulerOracle implementation that works with multiple backends through static
//! dispatch and monomorphization.
//!
//! # Zero-cost Abstraction
//!
//! The key insight is that the backend abstraction compiles away completely. When
//! you write:
//! ```rust
//! let scheduler = SchedulerOracle::<ProductionBackend, _>::new(...);
//! ```
//!
//! The Rust compiler generates specialized code where every `backend.method()` call
//! is inlined and optimized. It's as if you hand-wrote a ProductionScheduler with
//! no abstraction overhead.
//!
//! # The Dual-Backend Pattern
//!
//! We use the same pattern as VirtualClock and SimulatedMemory:
//! - **ProductionBackend**: Optimized for real-world use with dynamic capacity
//! - **VerificationBackend**: Bounded and stack-only for formal verification
//!
//! This lets us verify correctness on small models with Kani, then deploy the
//! same verified algorithm in production with different capacity limits.

use super::types::{SchedulerError, ThreadId, ThreadState};

/// Backend abstraction for thread state management
///
/// # TLA+ Correspondence
/// ```tla
/// VARIABLES threadStates
/// threadStates \in [Threads -> ThreadStates]
/// ```
///
/// # Design Contract
///
/// Implementations must maintain the following invariants:
///
/// 1. **Bounded Capacity**: `max_threads()` must return a consistent value
/// 2. **Valid States**: All thread IDs in [0, max_threads) must have a defined state
/// 3. **Initialization**: All threads start in RUNNABLE state (per TLA+ Init)
/// 4. **Thread Safety**: In production, must be safe for concurrent access
///
/// # Implementation Strategy
///
/// Different backends use different storage strategies:
///
/// - **ProductionBackend**: Uses `DashMap<ThreadId, ThreadState>` for concurrent
///   access with thousands of threads. Dynamic capacity, heap-allocated.
///
/// - **VerificationBackend**: Uses `RefCell<[ThreadState; MAX_THREADS]>` for
///   bounded model checking. Fixed capacity (typically 4), stack-allocated.
///
/// # Why a Trait?
///
/// We could use an enum with variants for Production and Verification, but the
/// trait approach has advantages:
///
/// 1. **Compile-time specialization**: Each backend gets its own optimized code path
/// 2. **Type-driven dispatch**: The type system ensures we can't mix backends
/// 3. **Future extensibility**: Easy to add new backends (e.g., distributed scheduler)
/// 4. **Clean separation**: Backend logic is isolated in separate modules
pub trait SchedulerBackend {
    /// Create a new backend with the specified number of threads
    ///
    /// # Arguments
    /// - `num_threads`: Number of threads to support
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Init ==
    ///     /\ threadStates = [t \in Threads |-> "RUNNABLE"]
    /// ```
    ///
    /// All threads are initialized to RUNNABLE state per the TLA+ specification.
    fn new(num_threads: usize) -> Self;

    /// Get the maximum number of threads this backend supports
    ///
    /// # Invariant
    ///
    /// This value must remain constant for the lifetime of the backend. Thread IDs
    /// are only valid in the range [0, max_threads()).
    fn max_threads(&self) -> usize;

    /// Get the current state of a thread
    ///
    /// # Arguments
    /// - `thread_id`: The thread to query
    ///
    /// # Returns
    /// - `Ok(ThreadState)`: Current state of the thread
    /// - `Err(SchedulerError::InvalidThreadId)`: Thread ID out of bounds
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// threadStates[t]
    /// ```
    ///
    /// # Performance Note
    ///
    /// This method is on the hot path - it's called for every event execution to
    /// check if the thread is runnable. Implementations should make this as fast
    /// as possible. In production, this means lock-free reads. In verification,
    /// this means direct array indexing.
    fn get_state(&self, thread_id: ThreadId) -> Result<ThreadState, SchedulerError>;

    /// Set the state of a thread
    ///
    /// # Arguments
    /// - `thread_id`: The thread to update
    /// - `new_state`: The new state to set
    ///
    /// # Returns
    /// - `Ok(ThreadState)`: The previous state of the thread
    /// - `Err(SchedulerError::InvalidThreadId)`: Thread ID out of bounds
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// threadStates' = [threadStates EXCEPT ![t] = new_state]
    /// ```
    ///
    /// # State Transition Validation
    ///
    /// Backends do not validate state transitions - that's the SchedulerOracle's
    /// responsibility. The backend is a simple storage mechanism. If you try to
    /// transition from COMPLETED to RUNNABLE (which makes no semantic sense), the
    /// backend will allow it. The oracle should prevent invalid transitions.
    ///
    /// # Performance Note
    ///
    /// This is called less frequently than `get_state` - typically only during
    /// explicit state changes (blocking, unblocking, completion). Still should
    /// be efficient, but not as critical as `get_state`.
    fn set_state(
        &self,
        thread_id: ThreadId,
        new_state: ThreadState,
    ) -> Result<ThreadState, SchedulerError>;

    /// Check if a thread is runnable without borrowing
    ///
    /// # Arguments
    /// - `thread_id`: The thread to check
    ///
    /// # Returns
    /// `true` if the thread exists and is in RUNNABLE state
    ///
    /// # Design Rationale
    ///
    /// This is a convenience method that combines `get_state()` and `is_runnable()`.
    /// We provide it as a trait method so backends can optimize it. For example,
    /// a backend might be able to check runnability without acquiring locks that
    /// `get_state()` would need.
    ///
    /// # Default Implementation
    ///
    /// The default implementation just calls `get_state()` and checks the result:
    /// ```rust
    /// fn is_runnable(&self, thread_id: ThreadId) -> bool {
    ///     self.get_state(thread_id)
    ///         .map(|state| state.is_runnable())
    ///         .unwrap_or(false)
    /// }
    /// ```
    ///
    /// Backends can override this if they have a more efficient implementation.
    #[inline(always)]
    fn is_runnable(&self, thread_id: ThreadId) -> bool {
        self.get_state(thread_id)
            .map(|state| state.is_runnable())
            .unwrap_or(false)
    }

    /// Get the count of threads in each state
    ///
    /// # Returns
    /// `(runnable_count, blocked_count, completed_count)`
    ///
    /// # Usage
    ///
    /// This is primarily for debugging and monitoring. It allows you to see how
    /// many threads are in each state without iterating yourself. The oracle can
    /// use this to decide if the simulation is deadlocked (all threads blocked)
    /// or complete (all threads completed).
    ///
    /// # Performance Note
    ///
    /// This method may require scanning all threads, so it can be expensive for
    /// large thread counts. Use it for diagnostics, not in hot paths.
    ///
    /// # Default Implementation
    ///
    /// The default implementation iterates all thread IDs and counts states.
    /// Backends that maintain counts as an invariant can override this for O(1)
    /// performance.
    fn state_counts(&self) -> (usize, usize, usize) {
        let mut runnable = 0;
        let mut blocked = 0;
        let mut completed = 0;

        for tid in 0..self.max_threads() {
            match self.get_state(ThreadId::new(tid)) {
                Ok(ThreadState::Runnable) => runnable += 1,
                Ok(ThreadState::Blocked) => blocked += 1,
                Ok(ThreadState::Completed) => completed += 1,
                Err(_) => {} // Thread doesn't exist, skip
            }
        }

        (runnable, blocked, completed)
    }

    /// Reset all threads to RUNNABLE state
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Init ==
    ///     /\ threadStates = [t \in Threads |-> "RUNNABLE"]
    /// ```
    ///
    /// # Usage
    ///
    /// This is used when resetting the scheduler to its initial state. It's
    /// called by `SchedulerOracle::reset()` to restore the Init condition from
    /// the TLA+ specification.
    ///
    /// # Default Implementation
    ///
    /// The default implementation sets each thread to RUNNABLE individually.
    /// Backends can override this if they have a more efficient bulk reset.
    fn reset(&self) {
        for tid in 0..self.max_threads() {
            let _ = self.set_state(ThreadId::new(tid), ThreadState::Runnable);
        }
    }
}

/// Extension trait for additional backend capabilities
///
/// # Design Rationale
///
/// Some backends might support additional features that aren't part of the core
/// contract. For example, a DistributedBackend might support querying which node
/// owns a thread. We put these in an extension trait to avoid cluttering the main
/// trait with optional features.
///
/// For Phase 1A, this trait is empty. In Phase 1B, we might add methods for:
/// - Resource ownership tracking
/// - Dependency graph queries
/// - Priority levels
pub trait SchedulerBackendExt: SchedulerBackend {
    // Future extensions will go here
}

// Blanket implementation: all SchedulerBackends automatically get the extension trait
impl<T: SchedulerBackend> SchedulerBackendExt for T {}

#[cfg(test)]
mod tests {
    use super::*;

    // We can't test the trait directly since it has no implementation
    // The actual tests will be in production_backend.rs and verification_backend.rs
    // This test module just documents the contract

    /// Test helper to verify backend contract compliance
    ///
    /// This is a generic test function that any backend implementation can use
    /// to verify it satisfies the contract. We'll call this from the specific
    /// backend test modules.
    #[allow(dead_code)]
    pub fn test_backend_contract<B: SchedulerBackend>(backend: B) {
        // Invariant: max_threads should be consistent
        let max_threads = backend.max_threads();
        assert_eq!(backend.max_threads(), max_threads);

        // Invariant: All threads should start RUNNABLE
        for tid in 0..max_threads {
            let state = backend.get_state(ThreadId::new(tid)).unwrap();
            assert_eq!(state, ThreadState::Runnable);
        }

        // Test state transitions
        if max_threads > 0 {
            let tid = ThreadId::new(0);
            
            // RUNNABLE -> BLOCKED
            let prev = backend.set_state(tid, ThreadState::Blocked).unwrap();
            assert_eq!(prev, ThreadState::Runnable);
            assert_eq!(backend.get_state(tid).unwrap(), ThreadState::Blocked);
            assert!(!backend.is_runnable(tid));

            // BLOCKED -> RUNNABLE
            let prev = backend.set_state(tid, ThreadState::Runnable).unwrap();
            assert_eq!(prev, ThreadState::Blocked);
            assert_eq!(backend.get_state(tid).unwrap(), ThreadState::Runnable);
            assert!(backend.is_runnable(tid));

            // RUNNABLE -> COMPLETED
            let prev = backend.set_state(tid, ThreadState::Completed).unwrap();
            assert_eq!(prev, ThreadState::Runnable);
            assert_eq!(backend.get_state(tid).unwrap(), ThreadState::Completed);
            assert!(!backend.is_runnable(tid));
        }

        // Test invalid thread ID
        let invalid_tid = ThreadId::new(max_threads + 100);
        assert!(backend.get_state(invalid_tid).is_err());
        assert!(backend.set_state(invalid_tid, ThreadState::Runnable).is_err());
        assert!(!backend.is_runnable(invalid_tid));

        // Test state counts
        if max_threads > 0 {
            backend.reset();
            let (runnable, blocked, completed) = backend.state_counts();
            assert_eq!(runnable, max_threads);
            assert_eq!(blocked, 0);
            assert_eq!(completed, 0);
        }
    }
}