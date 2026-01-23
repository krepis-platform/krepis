//! Ki-DPOR State Node (A* Node) with Liveness Tracking
//!
//! This module implements the ExecutionState from the TLA+ specification,
//! extended with fairness tracking for starvation detection.

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

/// Ki-DPOR State (ExecutionState in TLA+) with Liveness
///
/// # TLA+ Correspondence
///
/// ```tla
/// LivenessExecutionState == [
///     path: Seq(StepRecord),
///     cost_g: Nat,
///     heuristic_h: Nat,
///     priority_f: Nat,
///     resource_state: ...,
///     starvation_counters_state: [Threads -> Nat],  # NEW
///     fairness_score: Nat                            # NEW
/// ]
/// ```
///
/// # Liveness Properties
///
/// - `starvation_counters`: Steps since each thread made progress
/// - If counter exceeds MAX_STARVATION_LIMIT, we found a starvation bug
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
    
    // ========== Liveness Tracking ==========
    
    /// Starvation counters: steps since each thread executed
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// starvation_counters_state: [Threads -> Nat]
    /// ```
    ///
    /// Updated by: UpdateStarvationCounters(state, executed_thread)
    pub starvation_counters: Vec<usize>,
    
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
        let starvation_counters = vec![0; num_threads]; // All start at 0
        
        let state = Self {
            path: Vec::new(),
            cost_g: 0,
            heuristic_h: 0,
            priority_f: 0,
            resource_owners,
            waiting_queues,
            thread_status,
            clock_vectors,
            starvation_counters,
            state_hash: 0,
        };
        
        let mut state = state;
        state.recompute_heuristic();
        state.recompute_hash();
        state
    }
    
    /// Generate successor state
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// successor(curr, thread, op, res) == [
    ///     path |-> Append(curr.path, [thread |-> thread, op |-> op, res |-> res]),
    ///     cost_g |-> curr.cost_g + 1,
    ///     ...
    /// ]
    /// ```
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
        
        // Update starvation counters (CRITICAL FOR LIVENESS)
        new_state.update_starvation_counters(thread);
        
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
                    // Remove from waiting queue if present
                    self.waiting_queues[r].retain(|&waiting_thread| waiting_thread != thread);
                } else {
                    // Resource is held, block and add to queue (if not already there)
                    self.thread_status[t] = ThreadStatus::Blocked;
                    if !self.waiting_queues[r].contains(&thread) {
                        self.waiting_queues[r].push(thread);
                    }
                }
            }
            Operation::Release => {
                // Release resource (make it free)
                if self.resource_owners[r] == Some(thread) {
                    self.resource_owners[r] = None;
                    
                    // DO NOT automatically wake up waiters
                    // Let them compete in next Request operations
                    // This allows unfair scheduling and starvation scenarios
                }
            }
        }
        
        // Update vector clock
        self.clock_vectors[t].tick(thread);
    }
    
    /// Update starvation counters after a step
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// UpdateStarvationCounters(state, executed_thread) ==
    ///     [t \in Threads |->
    ///         IF t = executed_thread
    ///         THEN 0  \* Reset counter
    ///         ELSE IF state.thread_status_state[t] \in {"Running", "Blocked"}
    ///              THEN state.starvation_counters_state[t] + 1
    ///              ELSE state.starvation_counters_state[t]
    ///     ]
    /// ```
    fn update_starvation_counters(&mut self, executed_thread: ThreadId) {
        for (t_idx, counter) in self.starvation_counters.iter_mut().enumerate() {
            let thread = ThreadId(t_idx);
            
            if thread == executed_thread {
                // Reset counter for executing thread
                *counter = 0;
            } else {
                // Increment counter for threads that didn't execute
                // (but only if they're Running or Blocked)
                let status = self.thread_status[t_idx];
                if status == ThreadStatus::Running || status == ThreadStatus::Blocked {
                    *counter += 1;
                }
            }
        }
    }
    
    /// Compute heuristic value with fairness penalty
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// LivenessHeuristic(state) ==
    ///     LET danger_score == (blocked * 100) + (contention * 10) + (interleaving * 5)
    ///         total_starvation == TotalStarvation(state)
    ///         max_starvation == MaxStarvation(state)
    ///         fairness_score == (total_starvation * 50) + (max_starvation * 20)
    ///         combined_danger == danger_score + fairness_score
    ///         max_danger == 2000
    ///     IN max_danger - combined_danger
    /// ```
    ///
    /// # Philosophy
    ///
    /// To FIND starvation bugs, we must actively search for unfair paths.
    /// High starvation = LOWER h = HIGHER priority = Explored sooner.
    fn recompute_heuristic(&mut self) {
        // Original danger metrics
        let blocked_count = self.blocked_threads_count();
        let contention_score = self.contention_score();
        let interleaving_complexity = self.interleaving_complexity();
        
        let danger_score = (blocked_count * 100)
            + (contention_score * 10)
            + (interleaving_complexity * 5);
        
        // Fairness metrics (NEW)
        let total_starvation = self.total_starvation();
        let max_starvation = self.max_starvation();
        
        let fairness_score = (total_starvation * 50) + (max_starvation * 20);
        
        // Combined score
        let combined_danger = danger_score + fairness_score;
        
        // Invert so lower h = higher priority
        const MAX_DANGER: usize = 2000; // Increased to accommodate fairness terms
        self.heuristic_h = MAX_DANGER.saturating_sub(combined_danger);
    }
    
    /// Count blocked threads
    #[inline]
    fn blocked_threads_count(&self) -> usize {
        self.thread_status
            .iter()
            .filter(|&&status| status == ThreadStatus::Blocked)
            .count()
    }
    
    /// Calculate contention score (sum of waiting queue lengths)
    #[inline]
    fn contention_score(&self) -> usize {
        self.waiting_queues.iter().map(|q| q.len()).sum()
    }
    
    /// Calculate interleaving complexity (distinct threads in path)
    #[inline]
    fn interleaving_complexity(&self) -> usize {
        let mut threads = TinyBitSet::new(MAX_THREADS);
        for step in &self.path {
            threads.insert(step.thread.as_usize());
        }
        
        (0..MAX_THREADS)
            .filter(|&i| threads.contains(i))
            .count()
    }
    
    /// Total starvation (sum of all counters)
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// TotalStarvation(state) ==
    ///     LET counters == {state.starvation_counters_state[t] : t \in Threads}
    ///     IN SumSeq(SetToSeq(counters))
    /// ```
    #[inline]
    fn total_starvation(&self) -> usize {
        self.starvation_counters.iter().sum()
    }
    
    /// Maximum starvation (highest counter)
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// MaxStarvation(state) ==
    ///     LET counters == {state.starvation_counters_state[t] : t \in Threads}
    ///     IN CHOOSE max \in Nat : max \in counters /\ \A c \in counters : c <= max
    /// ```
    #[inline]
    fn max_starvation(&self) -> usize {
        *self.starvation_counters.iter().max().unwrap_or(&0)
    }
    
    /// Compute state signature hash
    fn recompute_hash(&mut self) {
        let mut hasher = DefaultHasher::new();
        
        for owner in &self.resource_owners {
            owner.hash(&mut hasher);
        }
        
        for status in &self.thread_status {
            status.hash(&mut hasher);
        }
        
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
    ///
    /// Returns threads that can make progress:
    /// - Running threads (always enabled)
    /// - Blocked threads (may try Request again when resource becomes free)
    pub fn enabled_threads(&self) -> Vec<ThreadId> {
    self.thread_status
        .iter()
        .enumerate()
        .filter_map(|(i, &status)| {
            match status {
                ThreadStatus::Running => Some(ThreadId(i)),
                ThreadStatus::Blocked => {
                    // Blocked threads are still "enabled" in the sense that
                    // they can attempt operations (retry Request)
                    Some(ThreadId(i))
                }
            }
        })
        .collect()
    }
    
}

// ============================================================================
// Ordering for BinaryHeap (Min-Heap behavior)
// ============================================================================

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
    fn test_initial_state_liveness() {
        let state = KiState::initial(2, 2);
        
        assert_eq!(state.starvation_counters.len(), 2);
        assert!(state.starvation_counters.iter().all(|&c| c == 0));
    }

    #[test]
    fn test_starvation_counter_update() {
        let mut state = KiState::initial(3, 2);
        
        // Thread 0 executes
        state.update_starvation_counters(ThreadId(0));
        
        // Thread 0 should be reset to 0
        assert_eq!(state.starvation_counters[0], 0);
        // Thread 1 and 2 should increment (they're Running but didn't execute)
        assert_eq!(state.starvation_counters[1], 1);
        assert_eq!(state.starvation_counters[2], 1);
        
        // Thread 0 executes again
        state.update_starvation_counters(ThreadId(0));
        
        assert_eq!(state.starvation_counters[0], 0);
        assert_eq!(state.starvation_counters[1], 2); // Keeps incrementing
        assert_eq!(state.starvation_counters[2], 2);
    }

    #[test]
    fn test_heuristic_with_starvation() {
        let mut state = KiState::initial(3, 2);
        
        let initial_h = state.heuristic_h;
        
        // Simulate starvation
        state.starvation_counters[1] = 5;
        state.starvation_counters[2] = 3;
        state.recompute_heuristic();
        
        // h should decrease (higher danger = lower h = higher priority)
        assert!(state.heuristic_h < initial_h);
    }

    #[test]
    fn test_fairness_metrics() {
        let mut state = KiState::initial(3, 2);
        
        state.starvation_counters[0] = 5;
        state.starvation_counters[1] = 3;
        state.starvation_counters[2] = 2;
        
        assert_eq!(state.total_starvation(), 10);
        assert_eq!(state.max_starvation(), 5);
    }

    #[test]
    fn test_successor_resets_executing_thread_counter() {
        let state = KiState::initial(2, 2);
        
        // Create successor where thread 0 executes
        let successor = state.successor(
            ThreadId(0),
            Operation::Request,
            ResourceId(0),
        );
        
        // Thread 0's counter should be 0
        assert_eq!(successor.starvation_counters[0], 0);
        // Thread 1's counter should be 1 (didn't execute)
        assert_eq!(successor.starvation_counters[1], 1);
    }
}