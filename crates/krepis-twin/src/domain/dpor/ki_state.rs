//! Ki-DPOR State Node (A* Node)
//!
//! This module implements the ExecutionState from the TLA+ specification,
//! representing a node in the A* search tree.

use super::scheduler::{Operation, StepRecord, TinyBitSet};
use super::vector_clock::VectorClock;
use super::MAX_THREADS;
use crate::domain::resources::{ResourceId, ThreadId};
use std::cmp::Ordering;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Thread status enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ThreadStatus {
    /// Thread is running
    Running,
    /// Thread is blocked on a resource
    Blocked,
}

/// Ki-DPOR State (ExecutionState in TLA+)
///
/// # TLA+ Correspondence
///
/// ```tla
/// ExecutionState == [
///     path: Seq(StepRecord),
///     cost_g: Nat,
///     heuristic_h: Nat,
///     priority_f: Nat,
///     resource_state: [Resources -> ResourceState],
///     waiting_queues_state: [Resources -> Seq(Threads)],
///     thread_status_state: [Threads -> ThreadStatusValues],
///     clock_state: [Threads -> [Threads -> Nat]]
/// ]
/// ```
///
/// # A* Properties
///
/// - `cost_g`: Actual cost from start (depth)
/// - `heuristic_h`: Estimated cost to goal (danger score)
/// - `priority_f`: Total priority (f = g + h)
///
/// Lower `priority_f` = higher priority = explored first
#[derive(Clone)]
pub struct KiState {
    /// Execution path (sequence of steps)
    pub path: Vec<StepRecord>,
    
    /// Actual cost from start (g in A*)
    pub cost_g: usize,
    
    /// Heuristic estimate (h in A*)
    pub heuristic_h: usize,
    
    /// Total priority (f = g + h in A*)
    pub priority_f: usize,
    
    // ========== State Snapshots ==========
    // A* requires full state restoration since we jump between branches
    
    /// Resource ownership snapshot
    /// None = free, Some(thread) = owned by thread
    pub resource_owners: Vec<Option<ThreadId>>,
    
    /// Waiting queues snapshot
    /// waiting_queues[r] = [t1, t2, ...] threads waiting for resource r
    pub waiting_queues: Vec<Vec<ThreadId>>,
    
    /// Thread status snapshot
    pub thread_status: Vec<ThreadStatus>,
    
    /// Vector clock snapshot
    pub clock_vectors: Vec<VectorClock>,
    
    /// Cached hash for state signature
    state_hash: u64,
}

impl KiState {
    /// Create initial state
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// initial_state == [
    ///     path |-> <<>>,
    ///     cost_g |-> 0,
    ///     heuristic_h |-> Heuristic(initial),
    ///     priority_f |-> 0,
    ///     ...
    /// ]
    /// ```
    pub fn initial(num_threads: usize, num_resources: usize) -> Self {
        let resource_owners = vec![None; num_resources];
        let waiting_queues = vec![Vec::new(); num_resources];
        let thread_status = vec![ThreadStatus::Running; num_threads];
        let clock_vectors = vec![VectorClock::new(); num_threads];
        
        let state = Self {
            path: Vec::new(),
            cost_g: 0,
            heuristic_h: 0, // Will be computed
            priority_f: 0,
            resource_owners,
            waiting_queues,
            thread_status,
            clock_vectors,
            state_hash: 0,
        };
        
        let mut state = state;
        state.recompute_heuristic();
        state.recompute_hash();
        state
    }
    
    /// Create successor state by applying an operation
    ///
    /// This is the core of A* expansion - generating child nodes.
    pub fn successor(
        &self,
        thread: ThreadId,
        operation: Operation,
        resource: ResourceId,
    ) -> Self {
        let mut new_state = self.clone();
        
        // Add step to path
        let step = StepRecord {
            thread,
            operation,
            resource,
            depth: self.path.len(),
            clock: self.clock_vectors[thread.as_usize()],
        };
        new_state.path.push(step);
        
        // Update cost
        new_state.cost_g = self.cost_g + 1;
        
        // Apply operation to snapshot
        new_state.apply_operation(thread, operation, resource);
        
        // Recompute heuristic and priority
        new_state.recompute_heuristic();
        new_state.priority_f = new_state.cost_g + new_state.heuristic_h;
        
        // Recompute hash
        new_state.recompute_hash();
        
        new_state
    }
    
    /// Apply an operation to the state snapshot
    fn apply_operation(&mut self, thread: ThreadId, operation: Operation, resource: ResourceId) {
        let r = resource.as_usize();
        let t = thread.as_usize();
        
        match operation {
            Operation::Request => {
                if self.resource_owners[r].is_none() {
                    // Resource is free, acquire it
                    self.resource_owners[r] = Some(thread);
                } else {
                    // Resource is held, block and add to queue
                    self.thread_status[t] = ThreadStatus::Blocked;
                    self.waiting_queues[r].push(thread);
                }
            }
            Operation::Release => {
                // Release resource
                if self.resource_owners[r] == Some(thread) {
                    // Check if there's a waiter
                    if let Some(next_thread) = self.waiting_queues[r].first().copied() {
                        // Wake up first waiter
                        self.resource_owners[r] = Some(next_thread);
                        self.thread_status[next_thread.as_usize()] = ThreadStatus::Running;
                        self.waiting_queues[r].remove(0);
                    } else {
                        // No waiters, just release
                        self.resource_owners[r] = None;
                    }
                }
            }
        }
        
        // Update vector clock
        self.clock_vectors[t].tick(thread);
    }
    
    /// Compute heuristic value (h in A*)
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// Heuristic(state) ==
    ///     LET blocked == BlockedThreadCount(state)
    ///         contention == ContentionScore(state)
    ///         interleaving == InterleaveComplexity(state)
    ///         danger_score == (blocked * 100) + (contention * 10) + (interleaving * 5)
    ///         max_danger == 1000
    ///     IN max_danger - danger_score
    /// ```
    ///
    /// # Implementation
    ///
    /// We compute a "danger score" where higher = more dangerous.
    /// Then invert it so lower h = higher priority.
    fn recompute_heuristic(&mut self) {
        let blocked_count = self.blocked_threads_count();
        let contention_score = self.contention_score();
        let interleaving_complexity = self.interleaving_complexity();
        
        // Danger score: higher = more dangerous = higher priority
        let danger_score = (blocked_count * 100)
            + (contention_score * 10)
            + (interleaving_complexity * 5);
        
        // Invert so lower h = higher priority
        const MAX_DANGER: usize = 1000;
        self.heuristic_h = MAX_DANGER.saturating_sub(danger_score);
    }
    
    /// Count blocked threads
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// BlockedThreadCount(state) ==
    ///     Cardinality({t \in Threads : state.thread_status_state[t] = "Blocked"})
    /// ```
    #[inline]
    fn blocked_threads_count(&self) -> usize {
        self.thread_status
            .iter()
            .filter(|&&status| status == ThreadStatus::Blocked)
            .count()
    }
    
    /// Calculate contention score (sum of waiting queue lengths)
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// ContentionScore(state) ==
    ///     SumSeq({Len(state.waiting_queues_state[r]) : r \in Resources})
    /// ```
    #[inline]
    fn contention_score(&self) -> usize {
        self.waiting_queues.iter().map(|q| q.len()).sum()
    }
    
    /// Calculate interleaving complexity (distinct threads in path)
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// InterleaveComplexity(state) ==
    ///     Cardinality({s.thread : s \in DOMAIN state.path})
    /// ```
    #[inline]
    fn interleaving_complexity(&self) -> usize {
        let mut threads = TinyBitSet::new(MAX_THREADS);
        for step in &self.path {
            threads.insert(step.thread.as_usize());
        }
        
        // Count set bits
        (0..MAX_THREADS)
            .filter(|&i| threads.contains(i))
            .count()
    }
    
    /// Compute state signature hash
    ///
    /// Used for detecting equivalent states (explored set).
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// StateSignature(state) ==
    ///     [resources |-> state.resource_state,
    ///      statuses |-> state.thread_status_state,
    ///      queues |-> state.waiting_queues_state]
    /// ```
    fn recompute_hash(&mut self) {
        let mut hasher = DefaultHasher::new();
        
        // Hash resource owners
        for owner in &self.resource_owners {
            owner.hash(&mut hasher);
        }
        
        // Hash thread status
        for status in &self.thread_status {
            status.hash(&mut hasher);
        }
        
        // Hash waiting queues
        for queue in &self.waiting_queues {
            queue.hash(&mut hasher);
        }
        
        self.state_hash = hasher.finish();
    }
    
    /// Get state signature hash
    pub fn signature(&self) -> u64 {
        self.state_hash
    }
    
    /// Get enabled (runnable) threads
    pub fn enabled_threads(&self) -> Vec<ThreadId> {
        self.thread_status
            .iter()
            .enumerate()
            .filter(|(_, &status)| status == ThreadStatus::Running)
            .map(|(i, _)| ThreadId(i))
            .collect()
    }
}

// ============================================================================
// Ordering for BinaryHeap (Min-Heap behavior)
// ============================================================================

/// Implement Ord for KiState to work with BinaryHeap
///
/// # Critical: Reverse Ordering
///
/// Rust's BinaryHeap is a MAX-heap (largest first).
/// A* needs a MIN-heap (smallest priority first).
///
/// Solution: Reverse the ordering.
/// - `self.f < other.f` returns `Ordering::Greater`
/// - This makes the heap pop the state with lowest f value.
impl Ord for KiState {
    fn cmp(&self, other: &Self) -> Ordering {
        // REVERSE: Lower priority_f = Greater ordering = Popped first
        other.priority_f.cmp(&self.priority_f)
    }
}

impl PartialOrd for KiState {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for KiState {
    fn eq(&self, other: &Self) -> bool {
        self.priority_f == other.priority_f
    }
}

impl Eq for KiState {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initial_state() {
        let state = KiState::initial(2, 2);
        
        assert_eq!(state.cost_g, 0);
        assert_eq!(state.path.len(), 0);
        assert_eq!(state.resource_owners.len(), 2);
        assert!(state.resource_owners.iter().all(|o| o.is_none()));
    }

    #[test]
    fn test_heuristic_blocked_threads() {
        let mut state = KiState::initial(3, 2);
        
        // Initially no blocked threads
        let initial_h = state.heuristic_h;
        
        // Block one thread
        state.thread_status[1] = ThreadStatus::Blocked;
        state.recompute_heuristic();
        
        // h should decrease (higher danger = lower h = higher priority)
        assert!(state.heuristic_h < initial_h);
    }

    #[test]
    fn test_ordering_min_heap() {
        let mut state1 = KiState::initial(2, 2);
        let mut state2 = KiState::initial(2, 2);
        
        state1.priority_f = 10;
        state2.priority_f = 5;
        
        // state2 has lower priority, should be "greater" (popped first)
        assert!(state2 > state1);
    }

    #[test]
    fn test_successor_generation() {
        let state = KiState::initial(2, 2);
        
        let successor = state.successor(
            ThreadId(0),
            Operation::Request,
            ResourceId(0),
        );
        
        assert_eq!(successor.cost_g, 1);
        assert_eq!(successor.path.len(), 1);
        assert_eq!(successor.resource_owners[0], Some(ThreadId(0)));
    }

    #[test]
    fn test_state_signature() {
        let state1 = KiState::initial(2, 2);
        let state2 = KiState::initial(2, 2);
        
        // Same initial state should have same signature
        assert_eq!(state1.signature(), state2.signature());
        
        // Different states should (likely) have different signatures
        let mut state3 = state1.clone();
        state3.resource_owners[0] = Some(ThreadId(0));
        state3.recompute_hash();
        
        assert_ne!(state1.signature(), state3.signature());
    }
}