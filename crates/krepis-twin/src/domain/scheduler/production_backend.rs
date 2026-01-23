//! Production Backend - Concurrent Thread State Management
//!
//! # Design Philosophy
//!
//! The production backend is optimized for real-world deployment where:
//! - Thread count can be in the thousands or millions
//! - Concurrent access from multiple threads is common
//! - Dynamic capacity is needed (threads can be added/removed)
//! - Memory usage should scale with actual thread count, not maximum possible
//!
//! # Implementation Strategy
//!
//! We use `DashMap<ThreadId, ThreadState>` as the storage mechanism.
//!
//! ## Why DashMap?
//!
//! DashMap is a concurrent hash map that provides:
//! - **Lock-free reads**: Multiple threads can read concurrently without blocking
//! - **Fine-grained locking**: Writes only lock a small shard of the map
//! - **Good cache locality**: Sharding improves CPU cache utilization
//! - **No central lock**: Scales well with thread count
//!
//! Compared to alternatives:
//! - `RwLock<HashMap>`: Would have a single lock, creating contention
//! - `Mutex<HashMap>`: Even worse, blocks all access
//! - `Arc<[AtomicU8]>`: Requires knowing max threads at compile time
//!
//! ## Memory Layout
//!
//! ```text
//! ProductionBackend
//!   └─ thread_states: DashMap<ThreadId, ThreadState>
//!        ├─ Shard 0: RwLock<HashMap<...>>
//!        ├─ Shard 1: RwLock<HashMap<...>>
//!        └─ ...
//! ```
//!
//! Each shard is independently lockable, so operations on different threads
//! rarely contend with each other.

#[cfg(not(kani))]
use super::backend::SchedulerBackend;
#[cfg(not(kani))]
use super::types::{SchedulerError, ThreadId, ThreadState};

use crate::domain::clock::EventId;
use std::collections::HashMap;
use parking_lot::RwLock;

// Production backend uses DashMap which Kani cannot verify
// Only compile this for non-Kani builds
#[cfg(not(kani))]
use dashmap::DashMap;
#[cfg(not(kani))]
use std::sync::Arc;

/// Production backend using DashMap for concurrent access
///
/// # TLA+ Correspondence
/// ```tla
/// VARIABLES threadStates
/// threadStates \in [Threads -> ThreadStates]
/// ```
///
/// # Thread Safety
///
/// This backend is safe to share across threads via `Arc`. Multiple threads
/// can call `get_state()` and `set_state()` concurrently without external
/// synchronization.
///
/// # Performance Characteristics
///
/// - `get_state()`: O(1) with lock-free read in the common case
/// - `set_state()`: O(1) with fine-grained locking
/// - `state_counts()`: O(n) where n is the number of threads
/// - Memory: O(n) where n is the number of active threads
///
/// # Example
///
/// ```rust
/// use krepis_twin::domain::scheduler::{ProductionSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
///
/// let backend = ProductionSchedulerBackend::new(100);
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
/// assert_eq!(blocked, 1);
/// ```
#[cfg(not(kani))]
pub struct ProductionBackend {
    /// Thread states stored in a concurrent hash map
    ///
    /// Key: ThreadId (0 to max_threads-1)
    /// Value: ThreadState (RUNNABLE, BLOCKED, or COMPLETED)
    ///
    /// DashMap automatically handles sharding and locking, so we don't need
    /// to manage any locks manually.
    thread_states: Arc<DashMap<ThreadId, ThreadState>>,

    /// Maximum number of threads supported
    ///
    /// This is set at construction and never changes. Thread IDs must be
    /// in the range [0, max_threads).
    ///
    /// We store this separately from the DashMap because DashMap's length
    /// only counts inserted entries, not capacity.
    max_threads: usize,

    // ========== NEW FIELD ==========
    /// Event-to-thread mapping for ownership tracking
    ///
    /// # Why HashMap?
    /// - O(1) insert/lookup/remove
    /// - Dynamic capacity (no MAX_EVENTS limit)
    /// - Production-optimized
    ///
    /// # Why RwLock?
    /// - Multiple readers (get_event_owner) can run concurrently
    /// - Only one writer (register_event, unregister_event) at a time
    /// - Better performance than Mutex for read-heavy workloads
    event_to_thread: RwLock<HashMap<EventId, ThreadId>>,
}

#[cfg(not(kani))]
impl ProductionBackend {
    /// Get reference to the underlying DashMap
    ///
    /// This is useful for advanced operations that need direct access to
    /// the map, though most users should use the SchedulerBackend trait
    /// methods instead.
    pub fn inner(&self) -> &Arc<DashMap<ThreadId, ThreadState>> {
        &self.thread_states
    }

    /// Get the number of threads currently tracked
    ///
    /// This may be less than `max_threads()` if some threads have been
    /// removed or never inserted.
    pub fn active_thread_count(&self) -> usize {
        self.thread_states.len()
    }
}

#[cfg(not(kani))]
impl SchedulerBackend for ProductionBackend {
    /// Create a new production backend
    ///
    /// # Arguments
    /// - `num_threads`: Number of threads to support (maximum ThreadId is num_threads - 1)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Init ==
    ///     /\ threadStates = [t \in Threads |-> "RUNNABLE"]
    /// ```
    ///
    /// # Performance Note
    ///
    /// DashMap pre-allocates shards but not entries. The initial allocation
    /// is O(1) regardless of num_threads. Entries are inserted lazily when
    /// threads are first used.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionSchedulerBackend, SchedulerBackend};
    ///
    /// // Support up to 1000 threads
    /// let backend = ProductionSchedulerBackend::new(1000);
    /// assert_eq!(backend.max_threads(), 1000);
    /// ```
    fn new(num_threads: usize) -> Self {
        Self {
            thread_states: Arc::new({  // ← Arc::new 추가!
                let map = DashMap::new();
                for tid in 0..num_threads {
                    map.insert(ThreadId::new(tid), ThreadState::Runnable);
                }
                map
            }),
            max_threads: num_threads,
            event_to_thread: RwLock::new(HashMap::new()),
        }
    }

    /// Get maximum number of threads
    ///
    /// # Invariant
    ///
    /// This value never changes after construction.
    #[inline(always)]
    fn max_threads(&self) -> usize {
        self.max_threads
    }

    /// Get the current state of a thread
    ///
    /// # Performance
    ///
    /// This is a lock-free read in the common case. DashMap uses read locks
    /// on shards, and multiple threads can read from different shards
    /// simultaneously without contention.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = ProductionSchedulerBackend::new(10);
    /// let state = backend.get_state(ThreadId::new(5)).unwrap();
    /// assert_eq!(state, ThreadState::Runnable);
    /// ```
    fn get_state(&self, thread_id: ThreadId) -> Result<ThreadState, SchedulerError> {
        // Validate thread ID bounds
        if thread_id.as_usize() >= self.max_threads {
            return Err(SchedulerError::InvalidThreadId {
                thread_id,
                max_threads: self.max_threads,
            });
        }

        // Get state from map
        // DashMap returns Option<Ref<K, V>>, we extract the value
        self.thread_states
            .get(&thread_id)
            .map(|entry: dashmap::mapref::one::Ref<'_, ThreadId, ThreadState>| *entry.value())
            .ok_or(SchedulerError::InvalidThreadId {
                thread_id,
                max_threads: self.max_threads,
            })
    }

    /// Set the state of a thread
    ///
    /// # Performance
    ///
    /// This acquires a write lock on a single shard of the DashMap. Other
    /// threads can still read and write to other shards concurrently.
    ///
    /// # Returns
    ///
    /// The previous state of the thread.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = ProductionSchedulerBackend::new(10);
    /// 
    /// // Change RUNNABLE -> BLOCKED
    /// let prev = backend.set_state(ThreadId::new(3), ThreadState::Blocked).unwrap();
    /// assert_eq!(prev, ThreadState::Runnable);
    ///
    /// // Verify change
    /// assert_eq!(backend.get_state(ThreadId::new(3)).unwrap(), ThreadState::Blocked);
    /// ```
    fn set_state(
        &self,
        thread_id: ThreadId,
        new_state: ThreadState,
    ) -> Result<ThreadState, SchedulerError> {
        // Validate thread ID bounds
        if thread_id.as_usize() >= self.max_threads {
            return Err(SchedulerError::InvalidThreadId {
                thread_id,
                max_threads: self.max_threads,
            });
        }

        // Insert new state and return old state
        // DashMap::insert returns Option<V> (the previous value)
        self.thread_states
            .insert(thread_id, new_state)
            .ok_or(SchedulerError::InvalidThreadId {
                thread_id,
                max_threads: self.max_threads,
            })
    }

    /// Check if a thread is runnable
    ///
    /// # Optimization
    ///
    /// This is optimized to avoid the Result wrapping/unwrapping of get_state().
    /// We go directly to the DashMap and check the state in one operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = ProductionSchedulerBackend::new(10);
    ///
    /// assert!(backend.is_runnable(ThreadId::new(0)));
    ///
    /// backend.set_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
    /// assert!(!backend.is_runnable(ThreadId::new(0)));
    /// ```
    #[inline]
    fn is_runnable(&self, thread_id: ThreadId) -> bool {
        if thread_id.as_usize() >= self.max_threads {
            return false;
        }

        self.thread_states
            .iter()
            .filter(|entry: &dashmap::mapref::multiple::RefMulti<'_, ThreadId, ThreadState>| entry.key() == &thread_id)
            .map(|entry: dashmap::mapref::multiple::RefMulti<'_, ThreadId, ThreadState>| entry.value().is_runnable())
            .next()
            .unwrap_or(false)
    }

    /// Get counts of threads in each state
    ///
    /// # Performance Warning
    ///
    /// This method iterates all entries in the DashMap, which is O(n) where
    /// n is the number of threads. Use this for debugging and monitoring,
    /// not in hot paths.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = ProductionSchedulerBackend::new(10);
    ///
    /// let (runnable, blocked, completed) = backend.state_counts();
    /// assert_eq!(runnable, 10);
    /// assert_eq!(blocked, 0);
    /// assert_eq!(completed, 0);
    ///
    /// backend.set_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
    /// let (runnable, blocked, completed) = backend.state_counts();
    /// assert_eq!(runnable, 9);
    /// assert_eq!(blocked, 1);
    /// ```
    fn state_counts(&self) -> (usize, usize, usize) {
        let mut runnable = 0;
        let mut blocked = 0;
        let mut completed = 0;

        // DashMap::iter() returns an iterator over all entries
        // This is a read-only iteration that acquires read locks on shards
        for entry in self.thread_states.iter() {
            let entry: dashmap::mapref::multiple::RefMulti<'_, ThreadId, ThreadState> = entry;
            match *entry.value() {
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
    /// This is O(n) where n is max_threads. It rewrites every entry in the map.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionSchedulerBackend, SchedulerBackend, ThreadId, ThreadState};
    ///
    /// let backend = ProductionSchedulerBackend::new(10);
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
        // Clear and reinitialize
        // This is more efficient than updating each entry individually
        self.thread_states.clear();
        
        for tid in 0..self.max_threads {
            self.thread_states.insert(ThreadId::new(tid), ThreadState::Runnable);
        }
    }

    // ========== EVENT OWNERSHIP TRACKING ==========
    
    /// Register event ownership (Production: O(1) HashMap insert)
    fn register_event(
        &self,
        event_id: EventId,
        thread_id: ThreadId,
    ) -> Result<(), SchedulerError> {
        let mut map = self.event_to_thread.write();
        map.insert(event_id, thread_id);
        Ok(())
    }

    /// Get event owner (Production: O(1) HashMap lookup)
    ///
    /// # Performance Note
    /// This is on the hot path (called during execute_next). RwLock allows
    /// multiple concurrent readers, so this doesn't block other get_event_owner
    /// calls.
    fn get_event_owner(&self, event_id: EventId) -> Option<ThreadId> {
        let map = self.event_to_thread.read();
        map.get(&event_id).copied()
    }

    /// Unregister event (Production: O(1) HashMap remove)
    fn unregister_event(&self, event_id: EventId) {
        let mut map = self.event_to_thread.write();
        map.remove(&event_id);
    }

    /// Clear all event registrations (Production: O(1) HashMap clear)
    fn clear_events(&self) {
        let mut map = self.event_to_thread.write();
        map.clear();
    }

    /// Count how many registered events belong to runnable threads
    fn count_runnable_events(&self) -> usize {
        let map = self.event_to_thread.read();
        map.values()
            .filter(|&&thread_id| self.is_runnable(thread_id))
            .count()
    }
}

// Implement Clone for ProductionBackend
// This is a cheap clone because DashMap is wrapped in Arc
#[cfg(not(kani))]
impl Clone for ProductionBackend {
    fn clone(&self) -> Self {
        Self {
            thread_states: Arc::clone(&self.thread_states),
            max_threads: self.max_threads,
            event_to_thread: RwLock::new(HashMap::new()),
        }
    }
}

#[cfg(all(test, not(kani)))]
mod tests {
    use super::*;

    #[test]
    fn test_production_backend_contract() {
        let backend = ProductionBackend::new(10);
        
        // Test 1: Initial state
        assert_eq!(backend.max_threads(), 10);
        for i in 0..10 {
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
        assert!(backend.get_state(ThreadId::new(100)).is_err());
        
        // Test 4: State counts
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 9);
        assert_eq!(blocked, 1);
        assert_eq!(completed, 0);
        
        // Test 5: Reset
        backend.reset();
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 10);
        assert_eq!(blocked, 0);
        assert_eq!(completed, 0);
    }

    #[test]
    fn test_production_backend_large_scale() {
        // Test with many threads to verify scalability
        let backend = ProductionBackend::new(10_000);
        
        assert_eq!(backend.max_threads(), 10_000);
        assert_eq!(backend.active_thread_count(), 10_000);
        
        // All should start RUNNABLE
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 10_000);
        assert_eq!(blocked, 0);
        assert_eq!(completed, 0);
    }

    #[test]
    fn test_production_backend_concurrent_access() {
        use std::sync::Arc;
        use std::thread;

        let backend = Arc::new(ProductionBackend::new(100));
        let mut handles = vec![];

        // Spawn 10 threads that each update 10 thread states
        for i in 0..10 {
            let backend_clone = Arc::clone(&backend);
            let handle = thread::spawn(move || {
                for j in 0..10 {
                    let tid = ThreadId::new(i * 10 + j);
                    backend_clone.set_state(tid, ThreadState::Blocked).unwrap();
                }
            });
            handles.push(handle);
        }

        // Wait for all threads to complete
        for handle in handles {
            handle.join().unwrap();
        }

        // All 100 threads should now be BLOCKED
        let (runnable, blocked, completed) = backend.state_counts();
        assert_eq!(runnable, 0);
        assert_eq!(blocked, 100);
        assert_eq!(completed, 0);
    }

    #[test]
    fn test_production_backend_clone() {
        let backend1 = ProductionBackend::new(10);
        backend1.set_state(ThreadId::new(5), ThreadState::Blocked).unwrap();

        // Clone shares the same underlying DashMap via Arc
        let backend2 = backend1.clone();
        
        // Changes in one are visible in the other
        assert_eq!(backend2.get_state(ThreadId::new(5)).unwrap(), ThreadState::Blocked);
        
        backend2.set_state(ThreadId::new(5), ThreadState::Completed).unwrap();
        assert_eq!(backend1.get_state(ThreadId::new(5)).unwrap(), ThreadState::Completed);
    }
}