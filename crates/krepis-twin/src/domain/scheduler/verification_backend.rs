//! Verification Backend - Bounded Thread State Management
//!
//! # Design Philosophy
//!
//! The verification backend is optimized for formal verification with Kani where:
//! - Thread count must be bounded at compile time
//! - All memory must be stack-allocated (no heap)
//! - State space must be small enough for exhaustive exploration
//! - Single-threaded execution (no concurrency)
//!
//! # Implementation Strategy
//!
//! We use a fixed-size array `[ThreadState; MAX_THREADS]` wrapped in `RefCell`.
//!
//! ## Why Fixed Array?
//!
//! Fixed arrays are:
//! - **Stack-allocated**: No heap allocation, Kani can verify
//! - **Bounded**: State space is finite and known at compile time
//! - **Fast**: Direct indexing, no hashing or traversal
//! - **Simple**: No complex data structures to reason about
//!
//! ## Why RefCell?
//!
//! RefCell provides:
//! - **Interior mutability**: Methods can take &self instead of &mut self
//! - **Runtime borrow checking**: Detects multiple mutable borrows
//! - **Single-threaded**: No thread safety overhead (not Send/Sync)
//!
//! This matches the verification use case perfectly - we don't need thread
//! safety, but we do need interior mutability for the SchedulerBackend trait.
//!
//! ## Memory Layout
//!
//! ```text
//! VerificationBackend
//!   └─ thread_states: RefCell<[ThreadState; MAX_THREADS]>
//!        └─ [Runnable, Runnable, Runnable, Runnable]  // All on stack
//! ```
//!
//! Total size: 4 bytes (one byte per ThreadState) + RefCell overhead (~16 bytes)
//!
//! # Kani Verification
//!
//! This backend is designed to work with Kani's bounded model checking:
//! - MAX_THREADS is small (typically 4)
//! - All possible thread state combinations can be explored
//! - No heap allocation means no allocation failures
//! - No concurrency means no race conditions to explore

use super::backend::SchedulerBackend;
use super::types::{SchedulerError, ThreadId, ThreadState};
use std::cell::RefCell;
use crate::domain::clock::EventId;

/// Maximum number of threads in verification mode
///
/// This is intentionally small to keep the state space manageable for
/// exhaustive verification. With 4 threads and 3 possible states per thread,
/// we have 3^4 = 81 possible thread state combinations to explore.
///
/// # Why 4?
///
/// 4 threads is enough to:
/// - Test basic scheduling logic
/// - Verify thread state transitions
/// - Detect simple race conditions
/// - Keep verification time reasonable (seconds to minutes)
///
/// But small enough to:
/// - Fit comfortably on the stack
/// - Allow exhaustive state space exploration
/// - Complete verification in CI/CD pipelines
pub const MAX_THREADS: usize = 4;

/// Maximum number of concurrent events for verification
///
/// # Why 16?
/// - Kani can handle bounded loops up to ~16 iterations comfortably
/// - 16 events is enough to test interesting scheduler scenarios
/// - Small enough to avoid state explosion
/// - 4 threads × 4 events each = reasonable workload
pub const MAX_EVENTS: usize = 16;

/// Verification backend using fixed array for bounded model checking
///
/// # TLA+ Correspondence
/// ```tla
/// VARIABLES threadStates
/// threadStates \in [Threads -> ThreadStates]
/// ```
///
/// With the constraint: `Cardinality(Threads) = MAX_THREADS`
///
/// # Thread Safety
///
/// This backend is **not thread-safe** and is **not Send/Sync**.
/// It is designed for single-threaded verification only.
///
/// # Performance Characteristics
///
/// - `get_state()`: O(1) direct array access
/// - `set_state()`: O(1) direct array write
/// - `state_counts()`: O(n) where n = MAX_THREADS (always 4)
/// - Memory: O(1) - fixed 4 bytes on stack
///
/// # Example
///
/// ```rust
/// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
///
/// let backend = VerificationSchedulerBackend::new(4);
///
/// // All threads start RUNNABLE
/// assert_eq!(backend.get_state(ThreadId::new(0)).unwrap(), ThreadState::Runnable);
///
/// // Change state
/// backend.set_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
/// assert_eq!(backend.get_state(ThreadId::new(0)).unwrap(), ThreadState::Blocked);
///
/// // Check counts
/// let (runnable, blocked, completed) = backend.state_counts();
/// assert_eq!(runnable, 3);
/// assert_eq!(blocked, 1);
/// ```
pub struct VerificationBackend {
    /// Thread states stored in a fixed-size array
    ///
    /// Index: ThreadId (0 to MAX_THREADS-1)
    /// Value: ThreadState (RUNNABLE, BLOCKED, or COMPLETED)
    ///
    /// RefCell allows interior mutability while maintaining borrow checking
    /// at runtime. This is safe because verification is single-threaded.
    thread_states: RefCell<[ThreadState; MAX_THREADS]>,

    /// Number of threads actually used
    ///
    /// This may be less than MAX_THREADS. For example, if you create a backend
    /// with new(2), only threads 0 and 1 are valid, even though the array has
    /// space for 4 threads.
    num_threads: usize,

    /// Event-to-thread mapping (bounded array)
    ///
    /// # Why Array Instead of HashMap/BTreeMap?
    /// - Kani can't handle HashMap (randomness)
    /// - Kani can't handle BTreeMap (complex tree operations)
    /// - Fixed array is simple and bounded
    /// - Linear search O(N) is fine when N=16
    ///
    /// # Storage Format
    /// Each element is (EventId, ThreadId). We use a parallel counter
    /// to track how many slots are used.
    event_to_thread: RefCell<[(EventId, ThreadId); MAX_EVENTS]>,
    
    /// Number of registered events
    ///
    /// # Invariant
    /// event_count <= MAX_EVENTS
    ///
    /// # Why Separate Counter?
    /// Array is fixed size, but we only use the first `event_count` elements.
    /// This avoids the need for Option<(EventId, ThreadId)> which would
    /// complicate Kani verification.
    event_count: RefCell<usize>,
}

impl VerificationBackend {
    /// Get a reference to the underlying array
    ///
    /// # Panics
    ///
    /// Panics if the RefCell is already mutably borrowed. This should never
    /// happen in correct single-threaded code.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend};
    ///
    /// let backend = VerificationSchedulerBackend::new(4);
    /// let states = backend.states();
    /// 
    /// // All 4 threads should be RUNNABLE
    /// assert_eq!(states.len(), 4);
    /// ```
    pub fn states(&self) -> std::cell::Ref<'_, [ThreadState; MAX_THREADS]> {
        self.thread_states.borrow()
    }

    /// Get the number of threads being used
    ///
    /// This is different from MAX_THREADS if the backend was created with
    /// a smaller num_threads.
    pub fn num_threads(&self) -> usize {
        self.num_threads
    }
}

impl SchedulerBackend for VerificationBackend {
    /// Create a new verification backend
    ///
    /// # Arguments
    /// - `num_threads`: Number of threads to support (must be ≤ MAX_THREADS)
    ///
    /// # Panics
    ///
    /// Panics if num_threads > MAX_THREADS. This is a precondition violation
    /// that should be caught during development, not at runtime.
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Init ==
    ///     /\ threadStates = [t \in Threads |-> "RUNNABLE"]
    /// ```
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend};
    ///
    /// // Create backend with 2 threads
    /// let backend = VerificationSchedulerBackend::new(2);
    /// assert_eq!(backend.max_threads(), 2);
    /// ```
    ///
    /// ```rust,should_panic
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend};
    ///
    /// // This will panic - too many threads
    /// let backend = VerificationSchedulerBackend::new(100);
    /// ```
    fn new(num_threads: usize) -> Self {
        assert!(
            num_threads <= MAX_THREADS,
            "VerificationBackend supports at most {} threads, requested {}",
            MAX_THREADS,
            num_threads
        );

        Self {
            thread_states: RefCell::new([ThreadState::Runnable; MAX_THREADS]),
            num_threads,
            event_to_thread: RefCell::new([(0, ThreadId::new(0)); MAX_EVENTS]),  // ← EventId::new(0) → 0
            event_count: RefCell::new(0),
        }
    }

    /// Get maximum number of threads
    ///
    /// # Invariant
    ///
    /// This value never changes after construction and is always ≤ MAX_THREADS.
    #[inline(always)]
    fn max_threads(&self) -> usize {
        self.num_threads
    }

    /// Get the current state of a thread
    ///
    /// # Performance
    ///
    /// This is a direct array access: `array[index]`. It doesn't get faster
    /// than this.
    ///
    /// # Panics
    ///
    /// Panics if the RefCell is already mutably borrowed. This should never
    /// happen in single-threaded verification code.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = VerificationSchedulerBackend::new(4);
    /// let state = backend.get_state(ThreadId::new(2)).unwrap();
    /// assert_eq!(state, ThreadState::Runnable);
    /// ```
    fn get_state(&self, thread_id: ThreadId) -> Result<ThreadState, SchedulerError> {
        // Validate thread ID bounds
        if thread_id.as_usize() >= self.num_threads {
            return Err(SchedulerError::InvalidThreadId {
                thread_id,
                max_threads: self.num_threads,
            });
        }

        // Direct array access through RefCell
        let states = self.thread_states.borrow();
        Ok(states[thread_id.as_usize()])
    }

    /// Set the state of a thread
    ///
    /// # Performance
    ///
    /// This is a direct array write: `array[index] = value`. As fast as it gets.
    ///
    /// # Panics
    ///
    /// Panics if the RefCell is already borrowed. This should never happen in
    /// single-threaded verification code.
    ///
    /// # Returns
    ///
    /// The previous state of the thread.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = VerificationSchedulerBackend::new(4);
    /// 
    /// // Change RUNNABLE -> BLOCKED
    /// let prev = backend.set_state(ThreadId::new(1), ThreadState::Blocked).unwrap();
    /// assert_eq!(prev, ThreadState::Runnable);
    ///
    /// // Verify change
    /// assert_eq!(backend.get_state(ThreadId::new(1)).unwrap(), ThreadState::Blocked);
    /// ```
    fn set_state(
        &self,
        thread_id: ThreadId,
        new_state: ThreadState,
    ) -> Result<ThreadState, SchedulerError> {
        // Validate thread ID bounds
        if thread_id.as_usize() >= self.num_threads {
            return Err(SchedulerError::InvalidThreadId {
                thread_id,
                max_threads: self.num_threads,
            });
        }

        // Get mutable access and swap state
        let mut states = self.thread_states.borrow_mut();
        let old_state = states[thread_id.as_usize()];
        states[thread_id.as_usize()] = new_state;
        
        Ok(old_state)
    }

    /// Check if a thread is runnable
    ///
    /// # Optimization
    ///
    /// Direct array access without Result wrapping.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = VerificationSchedulerBackend::new(4);
    ///
    /// assert!(backend.is_runnable(ThreadId::new(0)));
    ///
    /// backend.set_state(ThreadId::new(0), ThreadState::Completed).unwrap();
    /// assert!(!backend.is_runnable(ThreadId::new(0)));
    /// ```
    #[inline]
    fn is_runnable(&self, thread_id: ThreadId) -> bool {
        if thread_id.as_usize() >= self.num_threads {
            return false;
        }

        let states = self.thread_states.borrow();
        states[thread_id.as_usize()].is_runnable()
    }

    /// Get counts of threads in each state
    ///
    /// # Performance
    ///
    /// This is O(n) where n = num_threads (max 4). The loop is very small
    /// and will likely be unrolled by the compiler.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = VerificationSchedulerBackend::new(4);
    ///
    /// let (runnable, blocked, completed) = backend.state_counts();
    /// assert_eq!(runnable, 4);
    /// assert_eq!(blocked, 0);
    /// assert_eq!(completed, 0);
    ///
    /// backend.set_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
    /// backend.set_state(ThreadId::new(1), ThreadState::Completed).unwrap();
    ///
    /// let (runnable, blocked, completed) = backend.state_counts();
    /// assert_eq!(runnable, 2);
    /// assert_eq!(blocked, 1);
    /// assert_eq!(completed, 1);
    /// ```
    fn state_counts(&self) -> (usize, usize, usize) {
        let mut runnable = 0;
        let mut blocked = 0;
        let mut completed = 0;

        let states = self.thread_states.borrow();
        
        // Only count threads that are actually in use
        for i in 0..self.num_threads {
            match states[i] {
                ThreadState::Runnable => runnable += 1,
                ThreadState::Blocked => blocked += 1,
                ThreadState::Completed => completed += 1,
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
    /// # Performance
    ///
    /// This is O(n) where n = num_threads (max 4). Very fast.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{VerificationSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = VerificationSchedulerBackend::new(4);
    ///
    /// // Change some states
    /// backend.set_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
    /// backend.set_state(ThreadId::new(1), ThreadState::Completed).unwrap();
    ///
    /// // Reset
    /// backend.reset();
    ///
    /// // All should be RUNNABLE again
    /// assert_eq!(backend.get_state(ThreadId::new(0)).unwrap(), ThreadState::Runnable);
    /// assert_eq!(backend.get_state(ThreadId::new(1)).unwrap(), ThreadState::Runnable);
    /// ```
    fn reset(&self) {
        let mut states = self.thread_states.borrow_mut();
        
        // Reset all threads (including unused slots for simplicity)
        for state in states.iter_mut() {
            *state = ThreadState::Runnable;
        }
    }

    // ========== EVENT OWNERSHIP TRACKING ==========
    
    /// Register event ownership (Verification: O(1) array append)
    ///
    /// # Performance
    /// - Verification: O(1) append to array (if space available)
    /// - Fails if event_count >= MAX_EVENTS
    ///
    /// # Kani-Friendly
    /// - No heap allocation
    /// - No complex data structures
    /// - Just array[counter++] = value
    fn register_event(
        &self,
        event_id: EventId,
        thread_id: ThreadId,
    ) -> Result<(), SchedulerError> {
        let mut count = self.event_count.borrow_mut();
        
        // Check capacity
        if *count >= MAX_EVENTS {
            return Err(SchedulerError::QueueFull {
                max_events: MAX_EVENTS,  // ← capacity → max_events
                attempted: *count + 1,
            });
        }
        
        // Append to array
        let mut events = self.event_to_thread.borrow_mut();
        events[*count] = (event_id, thread_id);
        *count += 1;
        
        Ok(())
    }

    /// Get event owner (Verification: O(N) linear search, N=16)
    ///
    /// # Performance Note
    /// Linear search is acceptable because:
    /// - MAX_EVENTS = 16 (very small)
    /// - Array is cache-friendly
    /// - No allocation or complex logic
    /// - Kani can easily verify
    fn get_event_owner(&self, event_id: EventId) -> Option<ThreadId> {
        let count = *self.event_count.borrow();
        let events = self.event_to_thread.borrow();
        
        // Linear search through first `count` elements
        for i in 0..count {
            if events[i].0 == event_id {
                return Some(events[i].1);
            }
        }
        
        None
    }

    /// Unregister event (Verification: O(N) find + O(1) swap-remove)
    ///
    /// # Algorithm
    /// 1. Find event in array (O(N))
    /// 2. Swap with last element (O(1))
    /// 3. Decrement count (O(1))
    ///
    /// This maintains compactness without leaving holes.
    fn unregister_event(&self, event_id: EventId) {
        let mut count = self.event_count.borrow_mut();
        let mut events = self.event_to_thread.borrow_mut();
        
        // Find event
        for i in 0..*count {
            if events[i].0 == event_id {
                // Swap with last element
                *count -= 1;
                events[i] = events[*count];
                return;
            }
        }
        
        // Event not found - that's OK (idempotent)
    }

    /// Clear all event registrations (Verification: O(1) counter reset)
    ///
    /// # Performance
    /// We don't need to clear the array itself - just reset the counter.
    /// The "garbage" data beyond event_count is ignored.
    fn clear_events(&self) {
        let mut count = self.event_count.borrow_mut();
        *count = 0;
    }

    /// Count how many registered events belong to runnable threads
    fn count_runnable_events(&self) -> usize {
        let count = *self.event_count.borrow();
        let events = self.event_to_thread.borrow();
        
        let mut runnable_count = 0;
        for i in 0..count {
            let thread_id = events[i].1;
            if self.is_runnable(thread_id) {
                runnable_count += 1;
            }
        }
        runnable_count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_backend_contract() {
        let backend = VerificationBackend::new(4);
        
        // Test 1: Initial state
        assert_eq!(backend.max_threads(), 4);
        for i in 0..4 {
            assert_eq!(
                backend.get_state(ThreadId::new(i)).unwrap(),
                ThreadState::Runnable
            );
        }
        
        // Test 2: State transitions
        let prev = backend.set_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
        assert_eq!(prev, ThreadState::Runnable);
        assert_eq!(backend.get_state(ThreadId::new(0)).unwrap(), ThreadState::Blocked);
        
        // Test 3: Out of bounds
        assert!(backend.get_state(ThreadId::new(10)).is_err());
        
        // Test 4: State counts
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 3);
        assert_eq!(blocked, 1);
        assert_eq!(completed, 0);
        
        // Test 5: Reset
        backend.reset();
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 4);
        assert_eq!(blocked, 0);
        assert_eq!(completed, 0);
    }

    #[test]
    fn test_verification_backend_bounds() {
        let backend = VerificationBackend::new(2);
        
        assert_eq!(backend.max_threads(), 2);
        assert_eq!(backend.num_threads(), 2);
        
        // Threads 0 and 1 are valid
        assert!(backend.get_state(ThreadId::new(0)).is_ok());
        assert!(backend.get_state(ThreadId::new(1)).is_ok());
        
        // Thread 2 is out of bounds
        assert!(backend.get_state(ThreadId::new(2)).is_err());
    }

    #[test]
    #[should_panic(expected = "supports at most")]
    fn test_verification_backend_max_threads_exceeded() {
        // This should panic
        VerificationBackend::new(MAX_THREADS + 1);
    }

    #[test]
    fn test_verification_backend_state_transitions() {
        let backend = VerificationBackend::new(4);
        
        // Initial state
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 4);
        assert_eq!(blocked, 0);
        assert_eq!(completed, 0);
        
        // Transition thread 0: RUNNABLE -> BLOCKED
        backend.set_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 3);
        assert_eq!(blocked, 1);
        assert_eq!(completed, 0);
        
        // Transition thread 1: RUNNABLE -> COMPLETED
        backend.set_state(ThreadId::new(1), ThreadState::Completed).unwrap();
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 2);
        assert_eq!(blocked, 1);
        assert_eq!(completed, 1);
        
        // Transition thread 0: BLOCKED -> RUNNABLE
        backend.set_state(ThreadId::new(0), ThreadState::Runnable).unwrap();
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 3);
        assert_eq!(blocked, 0);
        assert_eq!(completed, 1);
    }

    #[test]
    fn test_verification_backend_stack_allocation() {
        // This test verifies that VerificationBackend is small enough to be
        // stack-allocated comfortably
        use std::mem::size_of;
        
        let size = size_of::<VerificationBackend>();
        
        // Should be very small: array of 4 bytes + RefCell overhead + usize
        // Typically around 24-32 bytes
        assert!(size < 64, "VerificationBackend is too large: {} bytes", size);
    }

    #[cfg(kani)]
    mod kani_proofs {
        use super::*;

        #[kani::proof]
        fn verify_get_state_bounds() {
            let backend = VerificationBackend::new(MAX_THREADS);
            let thread_id: usize = kani::any();
            
            if thread_id < MAX_THREADS {
                // Should succeed for valid thread IDs
                let result = backend.get_state(ThreadId::new(thread_id));
                assert!(result.is_ok());
            } else {
                // Should fail for invalid thread IDs
                let result = backend.get_state(ThreadId::new(thread_id));
                assert!(result.is_err());
            }
        }

        #[kani::proof]
        fn verify_state_transitions() {
            let backend = VerificationBackend::new(MAX_THREADS);
            let thread_id = ThreadId::new(0);
            
            // All possible state transitions should work
            let state: ThreadState = kani::any();
            let result = backend.set_state(thread_id, state);
            assert!(result.is_ok());
            assert_eq!(backend.get_state(thread_id).unwrap(), state);
        }

        #[kani::proof]
        fn verify_state_counts_invariant() {
            let backend = VerificationBackend::new(MAX_THREADS);
            
            let (runnable, blocked, completed) = backend.state_counts();
            
            // Invariant: sum of counts equals max_threads
            assert_eq!(runnable + blocked + completed, MAX_THREADS);
        }
    }
}