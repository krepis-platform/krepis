//! Ki-DPOR Scheduler (A* Based Exploration)
//!
//! This module implements the intelligent state space explorer that uses
//! A* search with a danger-based heuristic to find bugs faster.

use super::ki_state::{KiState};
use super::scheduler::{DporStats, Operation};
use crate::domain::resources::{ResourceId, ThreadId};
use std::collections::{BinaryHeap, HashSet};

/// Ki-DPOR Scheduler
///
/// # TLA+ Correspondence
///
/// ```tla
/// VARIABLES
///     priority_queue,     -> KiDporScheduler::open_set
///     explored_set,       -> KiDporScheduler::explored_hashes
///     current_state,      -> KiDporScheduler::current_state
///     stats               -> KiDporScheduler::stats
/// ```
///
/// # Algorithm
///
/// 1. Pop state with lowest priority from open_set
/// 2. Generate all successor states (enabled threads × operations)
/// 3. For each successor:
///    - Compute g, h, f
///    - If not explored, add to open_set
/// 4. Repeat until queue empty or bug found
///
/// # Key Difference from Classic DPOR
///
/// Classic DPOR uses a stack (DFS) and backtracks linearly.
/// Ki-DPOR uses a priority queue (Best-First) and jumps to most promising states.
pub struct KiDporScheduler {
    /// Priority queue (open set in A*)
    ///
    /// BinaryHeap is a max-heap, but we reversed Ord in KiState
    /// so it behaves as a min-heap (lowest priority_f first)
    open_set: BinaryHeap<KiState>,
    
    /// Explored state signatures (closed set in A*)
    ///
    /// Stores hash of state signature to avoid re-exploring
    explored_hashes: HashSet<u64>,
    
    /// Current state being expanded
    current_state: Option<KiState>,
    
    /// Number of threads
    #[allow(dead_code)]
    num_threads: usize,
    
    /// Number of resources
    #[allow(dead_code)]
    num_resources: usize,
    
    /// Statistics
    stats: DporStats,
}

impl KiDporScheduler {
    /// Create a new Ki-DPOR scheduler
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// KiDporInit ==
    ///     /\ priority_queue = <<initial_state>>
    ///     /\ explored_set = {}
    ///     /\ current_state = initial_state
    ///     /\ stats = [explored |-> 0, ...]
    /// ```
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
        }
    }
    
    /// Get next state to explore
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// ExpandState ==
    ///     /\ ~PQEmpty
    ///     /\ LET popped == PQPop(priority_queue)
    ///            curr == popped.state
    ///        IN current_state' = curr
    /// ```
    ///
    /// Returns None if exploration is complete (queue empty).
    pub fn next_state(&mut self) -> Option<&KiState> {
        if let Some(state) = self.open_set.pop() {
            // Mark as explored
            self.explored_hashes.insert(state.signature());
            self.stats.explored_states += 1;
            
            self.current_state = Some(state);
            self.current_state.as_ref()
        } else {
            None
        }
    }
    
    /// Generate and queue successor states
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// \A t \in enabled :
    ///     \E op \in Operations, r \in Resources :
    ///         LET new_state == [path |-> Append(curr.path, new_step), ...]
    ///             new_f == ComputePriority(new_g, new_h)
    ///         IN priority_queue' = PQInsert(remaining_pq, new_state)
    /// ```
    ///
    /// This is called after next_state() to expand the current node.
    pub fn expand_current<F>(&mut self, mut get_next_op: F)
    where
        F: FnMut(ThreadId, usize) -> Option<(Operation, ResourceId)>,
    {
        let current = match &self.current_state {
            Some(state) => state,
            None => return, // No current state
        };
        
        // Get enabled threads
        let enabled_threads = current.enabled_threads();
        
        for thread in enabled_threads {
            // Determine program counter for this thread
            let pc = current
                .path
                .iter()
                .filter(|step| step.thread == thread)
                .count();
            
            // Get next operation for this thread
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
        self.open_set.is_empty()
    }
    
    /// Get exploration statistics
    pub fn stats(&self) -> DporStats {
        self.stats
    }
    
    /// Get current state
    pub fn current(&self) -> Option<&KiState> {
        self.current_state.as_ref()
    }
    
    /// Get size of open set (for debugging)
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
    fn test_ki_scheduler_init() {
        let scheduler = KiDporScheduler::new(2, 2);
        
        assert_eq!(scheduler.open_set_size(), 1);
        assert!(!scheduler.is_complete());
    }

    #[test]
    fn test_next_state() {
        let mut scheduler = KiDporScheduler::new(2, 2);
        
        let state = scheduler.next_state();
        assert!(state.is_some());
        assert_eq!(scheduler.explored_count(), 1);
    }

    #[test]
    fn test_expand_simple() {
        let mut scheduler = KiDporScheduler::new(2, 2);
        
        // Get initial state
        scheduler.next_state();
        
        // Expand with simple operation generator
        scheduler.expand_current(|thread, pc| {
            if pc == 0 {
                Some((Operation::Request, ResourceId(thread.as_usize())))
            } else {
                None
            }
        });
        
        // Should have generated 2 successors (one per thread)
        assert!(scheduler.open_set_size() > 0);
    }

    #[test]
    fn test_exploration_cycle() {
        let mut scheduler = KiDporScheduler::new(2, 2);
        
        let mut steps = 0;
        const MAX_STEPS: usize = 10;
        
        while !scheduler.is_complete() && steps < MAX_STEPS {
            if scheduler.next_state().is_some() {
                scheduler.expand_current(|thread, pc| {
                    if pc == 0 {
                        Some((Operation::Request, ResourceId(thread.as_usize())))
                    } else {
                        None
                    }
                });
            }
            steps += 1;
        }
        
        assert!(scheduler.stats().explored_states > 0);
    }
}