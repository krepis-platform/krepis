//! DetailedTracker - Full Tracking for Verification

use super::tracker::*;
use super::types::*;
use std::collections::VecDeque;

/// Maximum threads for verification (matches TLA+ constant)
pub const MAX_THREADS: usize = 8;

/// Maximum resources for verification (matches TLA+ constant)
pub const MAX_RESOURCES: usize = 8;

/// Detailed resource tracker for verification
///
/// # TLA+ Correspondence
///
/// ```tla
/// VARIABLES
///     resources: [Resource -> [owner: Thread | Null, count: Nat]]
///     waiting_queues: [Resource -> Seq(Thread)]
///     wait_for_graph: [Thread -> SUBSET Threads]
///     thread_status: [Thread -> {"Running", "Blocked", "Finished"}]
/// ```
///
/// # Data Structures
///
/// - **Adjacency Matrix** for wait-for graph (O(1) cycle check prep)
/// - **Fixed-size arrays** for Kani verification compatibility
/// - **VecDeque** for FIFO waiting queues
pub struct DetailedTracker {
    /// Number of threads
    num_threads: usize,
    
    /// Number of resources
    num_resources: usize,
    
    /// Resource ownership: resources[r] = Some(thread) or None
    /// TLA+: resources[r].owner
    resources: [Option<ThreadId>; MAX_RESOURCES],
    
    /// Waiting queues: waiting_queues[r] = [t1, t2, ...]
    /// TLA+: waiting_queues[r]
    waiting_queues: [VecDeque<ThreadId>; MAX_RESOURCES],
    
    /// Wait-for graph as adjacency matrix: wait_for_graph[t1][t2] = true
    /// means t1 waits for t2
    /// TLA+: wait_for_graph[t] = {threads that t waits for}
    wait_for_graph: [[bool; MAX_THREADS]; MAX_THREADS],
    
    /// Thread status
    /// TLA+: thread_status[t]
    thread_status: [ThreadStatus; MAX_THREADS],
    
    /// Context switch counter (for interleaving score)
    context_switches: u32,
}

impl DetailedTracker {
    /// Check if adding edge (from -> to) would create a cycle
    ///
    /// # TLA+ Correspondence
    ///
    /// This implements the cycle detection logic from HasCycle:
    /// ```tla
    /// HasCycle == \E t \in Threads : t \in TransitiveClosure(wait_for_graph)[t]
    /// ```
    ///
    /// # Algorithm
    ///
    /// Floyd's cycle detection (O(V + E) time, O(1) space)
    fn would_create_cycle(&self, from: ThreadId, to: ThreadId) -> Option<Vec<ThreadId>> {
        if from == to {
            return Some(vec![from]); // Self-loop
        }
        
        // DFS from 'to' to see if we can reach 'from'
        let mut visited = [false; MAX_THREADS];
        let mut path = Vec::new();
        
        if self.dfs_find_path(to, from, &mut visited, &mut path) {
            // Found path from 'to' to 'from'
            // Adding edge 'from -> to' would complete the cycle
            path.push(from); // Complete the cycle
            Some(path)
        } else {
            None
        }
    }

    /// DFS to find path from start to target
    fn dfs_find_path(
        &self,
        current: ThreadId,
        target: ThreadId,
        visited: &mut [bool; MAX_THREADS],
        path: &mut Vec<ThreadId>,
    ) -> bool {
        if current == target {
            path.push(current);
            return true;
        }
        
        if visited[current.as_usize()] {
            return false;
        }
        
        visited[current.as_usize()] = true;
        path.push(current);
        
        // Follow wait-for edges
        for next_id in 0..self.num_threads {
            if self.wait_for_graph[current.as_usize()][next_id] {
                if self.dfs_find_path(ThreadId(next_id), target, visited, path) {
                    return true;
                }
            }
        }
        
        path.pop();
        false
    }
    
    /// Find all cycles in wait-for graph
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// DeadlockedThreads == {t \in Threads : t \in TransitiveClosure(wait_for_graph)[t]}
    /// ```
    fn find_cycles(&self) -> Vec<Vec<ThreadId>> {
        let mut cycles = Vec::new();
        
        for start in 0..self.num_threads {
            let start_id = ThreadId(start);
            
            // Skip if not in wait-for graph
            let has_outgoing = (0..self.num_threads)
                .any(|i| self.wait_for_graph[start][i]);
            
            if !has_outgoing {
                continue;
            }
            
            let mut visited = [false; MAX_THREADS];
            let mut path = Vec::new();
            
            if self.dfs_cycle(start_id, start_id, &mut visited, &mut path, true) {
                cycles.push(path);
            }
        }
        
        cycles
    }
    
    fn dfs_cycle(
        &self,
        current: ThreadId,
        target: ThreadId,
        visited: &mut [bool; MAX_THREADS],
        path: &mut Vec<ThreadId>,
        is_start: bool,
    ) -> bool {
        if !is_start && current == target {
            return true; // Found cycle!
        }
        
        if visited[current.as_usize()] {
            return false;
        }
        
        visited[current.as_usize()] = true;
        path.push(current);
        
        for next_id in 0..self.num_threads {
            if self.wait_for_graph[current.as_usize()][next_id] {
                if self.dfs_cycle(ThreadId(next_id), target, visited, path, false) {
                    return true;
                }
            }
        }
        
        path.pop();
        false
    }
}

impl ResourceTracker for DetailedTracker {
    fn new(num_threads: usize, num_resources: usize) -> Self {
        assert!(num_threads <= MAX_THREADS, "Too many threads");
        assert!(num_resources <= MAX_RESOURCES, "Too many resources");
        
        Self {
            num_threads,
            num_resources,
            resources: [None; MAX_RESOURCES],
            waiting_queues: Default::default(),
            wait_for_graph: [[false; MAX_THREADS]; MAX_THREADS],
            thread_status: [ThreadStatus::Running; MAX_THREADS],
            context_switches: 0,
        }
    }

    fn request(
        &mut self,
        thread: ThreadId,
        resource: ResourceId,
    ) -> Result<RequestResult, ResourceError> {
        // Validate bounds
        if thread.as_usize() >= self.num_threads {
            return Err(ResourceError::InvalidThreadId(thread));
        }
        
        if resource.as_usize() >= self.num_resources {
            return Err(ResourceError::InvalidResourceId(resource));
        }
        
        let r = resource.as_usize();
        
        // TLA+ fix: Prevent self-deadlock
        if self.resources[r] == Some(thread) {
            return Err(ResourceError::AlreadyOwned { thread, resource });
        }
        
        // Check if resource is available
        if let Some(owner) = self.resources[r] {
            // Resource is held, must block
            
            // Check if adding this edge would create a cycle
            if let Some(cycle) = self.would_create_cycle(thread, owner) {
                return Err(ResourceError::DeadlockDetected { cycle });
            }
            
            // Add to waiting queue
            self.waiting_queues[r].push_back(thread);
            
            // Update wait-for graph
            self.wait_for_graph[thread.as_usize()][owner.as_usize()] = true;
            
            // Update thread status
            self.thread_status[thread.as_usize()] = ThreadStatus::Blocked;
            
            // Track context switch
            self.context_switches += 1;
            
            Ok(RequestResult::Blocked)
        } else {
            // Resource is free, acquire immediately
            self.resources[r] = Some(thread);
            
            Ok(RequestResult::Acquired)
        }
    }

    fn release(
        &mut self,
        thread: ThreadId,
        resource: ResourceId,
    ) -> Result<(), ResourceError> {
        // Validate bounds
        if thread.as_usize() >= self.num_threads {
            return Err(ResourceError::InvalidThreadId(thread));
        }
        
        if resource.as_usize() >= self.num_resources {
            return Err(ResourceError::InvalidResourceId(resource));
        }
        
        let r = resource.as_usize();
        
        // Check ownership
        if self.resources[r] != Some(thread) {
            return Err(ResourceError::NotOwned { thread, resource });
        }
        
        // TLA+ ReleaseResource logic
        if let Some(next_thread) = self.waiting_queues[r].pop_front() {
            // Wake up next waiter
            // TLA+ resources' = [resources EXCEPT ![r].owner = next_thread]
            self.resources[r] = Some(next_thread);
            
            // TLA+ thread_status' = [thread_status EXCEPT ![next_thread] = "Running"]
            self.thread_status[next_thread.as_usize()] = ThreadStatus::Running;
            
            // TLA+ wait_for_graph' = [wait_for_graph EXCEPT ![next_thread] = @ \ {t}]
            self.wait_for_graph[next_thread.as_usize()][thread.as_usize()] = false;
            
            self.context_switches += 1;
        } else {
            // No waiters, just release
            // TLA+ resources' = [resources EXCEPT ![r].owner = Null]
            self.resources[r] = None;
        }
        
        Ok(())
    }

    fn on_finish(&mut self, thread: ThreadId) -> Result<(), ResourceError> {
        if thread.as_usize() >= self.num_threads {
            return Err(ResourceError::InvalidThreadId(thread));
        }
        
        // TLA+ fix: Check if thread still holds any resources
        let held: Vec<ResourceId> = (0..self.num_resources)
            .filter(|&r| self.resources[r] == Some(thread))
            .map(ResourceId)
            .collect();
        
        if !held.is_empty() {
            return Err(ResourceError::ResourceLeak {
                thread,
                held_resources: held,
            });
        }
        
        // TLA+ thread_status' = [thread_status EXCEPT ![t] = "Finished"]
        self.thread_status[thread.as_usize()] = ThreadStatus::Finished;
        
        Ok(())
    }

    fn has_deadlock(&self) -> bool {
        // TLA+ HasCycle
        !self.find_cycles().is_empty()
    }

    fn deadlocked_threads(&self) -> Vec<ThreadId> {
        // TLA+ DeadlockedThreads
        let cycles = self.find_cycles();
        let mut threads = std::collections::HashSet::new();
        
        for cycle in cycles {
            for t in cycle {
                threads.insert(t);
            }
        }
        
        threads.into_iter().collect()
    }

    fn contention_score(&self) -> u32 {
        // TLA+ ContentionScore: Sum of waiting queue lengths
        self.waiting_queues
            .iter()
            .take(self.num_resources)
            .map(|q| q.len() as u32)
            .sum()
    }

    fn interleaving_score(&self) -> u32 {
        // Context switches count
        self.context_switches
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_acquire_release() {
        let mut tracker = DetailedTracker::new(2, 2);
        
        // Thread 0 acquires resource 0
        assert_eq!(
            tracker.request(ThreadId(0), ResourceId(0)).unwrap(),
            RequestResult::Acquired
        );
        
        // Thread 0 releases resource 0
        tracker.release(ThreadId(0), ResourceId(0)).unwrap();
        
        assert!(!tracker.has_deadlock());
    }

    #[test]
    fn test_self_deadlock_prevention() {
        let mut tracker = DetailedTracker::new(2, 2);
        
        // Thread 0 acquires resource 0
        tracker.request(ThreadId(0), ResourceId(0)).unwrap();
        
        // Thread 0 tries to acquire resource 0 again -> Error
        let result = tracker.request(ThreadId(0), ResourceId(0));
        assert!(matches!(result, Err(ResourceError::AlreadyOwned { .. })));
    }

    #[test]
    fn test_ab_ba_deadlock_detection() {
        let mut tracker = DetailedTracker::new(2, 2);
        
        // Thread 0 acquires r0
        tracker.request(ThreadId(0), ResourceId(0)).unwrap();
        
        // Thread 1 acquires r1
        tracker.request(ThreadId(1), ResourceId(1)).unwrap();
        
        // Thread 0 tries r1 -> Blocked
        assert_eq!(
            tracker.request(ThreadId(0), ResourceId(1)).unwrap(),
            RequestResult::Blocked
        );
        
        // Thread 1 tries r0 -> DEADLOCK!
        let result = tracker.request(ThreadId(1), ResourceId(0));
        assert!(matches!(result, Err(ResourceError::DeadlockDetected { .. })));
    }

    #[test]
    fn test_resource_leak_detection() {
        let mut tracker = DetailedTracker::new(2, 2);
        
        // Thread 0 acquires resource 0
        tracker.request(ThreadId(0), ResourceId(0)).unwrap();
        
        // Thread 0 tries to finish without releasing -> Error
        let result = tracker.on_finish(ThreadId(0));
        assert!(matches!(result, Err(ResourceError::ResourceLeak { .. })));
    }
}