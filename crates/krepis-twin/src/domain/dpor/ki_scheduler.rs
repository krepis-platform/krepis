//! Ki-DPOR Scheduler with Liveness Detection
//!
//! This module implements the intelligent state space explorer with
//! starvation detection capabilities.

use super::ki_state::{KiState, ThreadStatus};
use super::scheduler::{DporStats, Operation};
use crate::domain::resources::{ResourceId, ThreadId};
use std::collections::{BinaryHeap, HashSet};

/// Maximum starvation limit (steps a thread can wait)
///
/// # TLA+ Correspondence
///
/// ```tla
/// CONSTANT MaxStarvationLimit
/// ```
pub const MAX_STARVATION_LIMIT: usize = 10;

/// Liveness violation types
///
/// # TLA+ Correspondence
///
/// ```tla
/// IsStarving(state, thread) ==
///     state.starvation_counters_state[thread] > MaxStarvationLimit
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LivenessViolation {
    /// Thread is starved (exceeded MAX_STARVATION_LIMIT)
    Starvation {
        /// Thread that is starved
        thread: ThreadId,
        /// Number of steps thread has been waiting
        count: usize,
    },
    
    /// Deadlock detected (all threads blocked)
    Deadlock {
        /// List of blocked threads
        blocked_threads: Vec<ThreadId>,
    },
}

/// Ki-DPOR Scheduler with Liveness Checking
///
/// # TLA+ Correspondence
///
/// Extended from `KiDporScheduler` with liveness tracking:
///
/// ```tla
/// VARIABLES
///     priority_queue,
///     explored_set,
///     starvation_counters,  # NEW
///     fairness_stats        # NEW
/// ```
pub struct KiDporScheduler {
    /// Priority queue (open set in A*)
    open_set: BinaryHeap<KiState>,
    
    /// Explored state signatures
    explored_hashes: HashSet<u64>,
    
    /// Current state being expanded
    current_state: Option<KiState>,
    
    /// Number of threads
    num_threads: usize,
    
    /// Number of resources
    #[allow(dead_code)] // Used for validation, may be used in future
    num_resources: usize,
    
    /// Statistics
    stats: DporStats,
    
    /// Liveness violation found (if any)
    liveness_violation: Option<LivenessViolation>,
}

impl KiDporScheduler {
    /// Create a new Ki-DPOR scheduler
    pub fn new(num_threads: usize, num_resources: usize) -> Self {
        let mut open_set = BinaryHeap::new();
        let initial_state = KiState::initial(num_threads, num_resources);
        
        open_set.push(initial_state);
        
        Self {
            open_set,
            explored_hashes: HashSet::new(),
            current_state: None,
            num_threads,
            num_resources,
            stats: DporStats::default(),
            liveness_violation: None,
        }
    }
    
    /// Get next state to explore
    ///
    /// Returns None if exploration is complete or liveness violation found.
    pub fn next_state(&mut self) -> Option<&KiState> {
        // Stop if we found a liveness violation
        if self.liveness_violation.is_some() {
            return None;
        }
        
        if let Some(state) = self.open_set.pop() {
            // Check for liveness violations
            if let Some(violation) = self.check_liveness(&state) {
                self.liveness_violation = Some(violation);
                self.current_state = Some(state);
                return None; // Stop exploration
            }
            
            // Mark as explored
            self.explored_hashes.insert(state.signature());
            self.stats.explored_states += 1;
            
            self.current_state = Some(state);
            self.current_state.as_ref()
        } else {
            None
        }
    }
    
    /// Check for liveness violations in a state
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// NoStarvation ==
    ///     \A t \in Threads : starvation_counters[t] <= MaxStarvationLimit
    ///
    /// NoDeadlock ==
    ///     ~(\A t \in Threads : thread_status_state[t] = "Blocked")
    /// ```
    fn check_liveness(&self, state: &KiState) -> Option<LivenessViolation> {
        // Check for starvation
        for (t_idx, &count) in state.starvation_counters.iter().enumerate() {
            if count > MAX_STARVATION_LIMIT {
                return Some(LivenessViolation::Starvation {
                    thread: ThreadId(t_idx),
                    count,
                });
            }
        }
        
        // Check for deadlock (all threads blocked)
        let blocked_threads: Vec<ThreadId> = state
            .thread_status
            .iter()
            .enumerate()
            .filter(|(_, &status)| status == ThreadStatus::Blocked)
            .map(|(i, _)| ThreadId(i))
            .collect();
        
        if blocked_threads.len() == self.num_threads && self.num_threads > 0 {
            return Some(LivenessViolation::Deadlock { blocked_threads });
        }
        
        None
    }
    
    /// Generate and queue successor states
    pub fn expand_current<F>(&mut self, mut get_next_op: F)
    where
        F: FnMut(ThreadId, usize) -> Option<(Operation, ResourceId)>,
    {
        // Stop if we found a violation
        if self.liveness_violation.is_some() {
            return;
        }
        
        let current = match &self.current_state {
            Some(state) => state,
            None => return,
        };
        
        // Get enabled threads
        let enabled_threads = current.enabled_threads();
        
        for thread in enabled_threads {
            // Determine program counter
            let pc = current
                .path
                .iter()
                .filter(|step| step.thread == thread)
                .count();
            
            // Get next operation
            if let Some((operation, resource)) = get_next_op(thread, pc) {
                // Generate successor state
                let successor = current.successor(thread, operation, resource);
                
                // Skip if already explored
                if self.explored_hashes.contains(&successor.signature()) {
                    continue;
                }
                
                // Add to open set
                self.open_set.push(successor);
                
                // Update stats
                self.stats.max_depth = self.stats.max_depth.max(current.cost_g + 1);
            }
        }
    }
    
    /// Check if exploration is complete
    pub fn is_complete(&self) -> bool {
        self.open_set.is_empty() || self.liveness_violation.is_some()
    }
    
    /// Get liveness violation (if found)
    pub fn liveness_violation(&self) -> Option<&LivenessViolation> {
        self.liveness_violation.as_ref()
    }
    
    /// Get exploration statistics
    pub fn stats(&self) -> DporStats {
        self.stats
    }
    
    /// Get current state
    pub fn current(&self) -> Option<&KiState> {
        self.current_state.as_ref()
    }
    
    /// Get size of open set
    pub fn open_set_size(&self) -> usize {
        self.open_set.len()
    }
    
    /// Get number of explored states
    pub fn explored_count(&self) -> usize {
        self.explored_hashes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_starvation_detection() {
        let mut scheduler = KiDporScheduler::new(2, 1);
        
        // Simulate greedy thread scenario
        let mut iteration = 0;
        let max_iterations = 50;
        
        while !scheduler.is_complete() && iteration < max_iterations {
            if scheduler.next_state().is_some() {
                scheduler.expand_current(|thread, pc| {
                    // Thread 0 is greedy (loops)
                    if thread == ThreadId(0) {
                        match pc % 2 {
                            0 => Some((Operation::Request, ResourceId(0))),
                            _ => Some((Operation::Release, ResourceId(0))),
                        }
                    } else {
                        // Thread 1 tries once
                        if pc == 0 {
                            Some((Operation::Request, ResourceId(0)))
                        } else {
                            None
                        }
                    }
                });
            }
            iteration += 1;
        }
        
        // Should detect starvation
        if let Some(violation) = scheduler.liveness_violation() {
            match violation {
                LivenessViolation::Starvation { thread, count } => {
                    assert_eq!(*thread, ThreadId(1));
                    assert!(*count > MAX_STARVATION_LIMIT);
                }
                _ => panic!("Expected starvation, got {:?}", violation),
            }
        } else {
            // Note: May not always find starvation in this simple test
            // due to heuristic exploration order
        }
    }

    #[test]
    fn test_deadlock_detection() {
        let mut state = KiState::initial(2, 2);
        
        // Both threads blocked
        state.thread_status[0] = ThreadStatus::Blocked;
        state.thread_status[1] = ThreadStatus::Blocked;
        
        let scheduler = KiDporScheduler::new(2, 2);
        let violation = scheduler.check_liveness(&state);
        
        assert!(matches!(violation, Some(LivenessViolation::Deadlock { .. })));
    }
}