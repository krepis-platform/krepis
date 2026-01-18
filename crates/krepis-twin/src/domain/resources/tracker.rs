//! ResourceTracker Trait - Common Interface

use super::types::*;

/// Resource tracking interface
///
/// # TLA+ Correspondence
///
/// This trait corresponds to the actions in ResourceOracle.tla:
/// - `request()` -> RequestResource(t, r)
/// - `release()` -> ReleaseResource(t, r)
/// - `on_finish()` -> Finish(t)
///
/// # Zero-Cost Abstraction
///
/// In production builds (`#[cfg(not(feature = "twin"))]`), this trait
/// is implemented by NoOpTracker with all methods inlined and empty.
/// The compiler removes all calls completely.
///
/// In verification builds (`#[cfg(feature = "twin")]`), this trait
/// is implemented by DetailedTracker with full tracking logic.
pub trait ResourceTracker {
    /// Create a new tracker
    ///
    /// # Arguments
    /// - `num_threads`: Number of threads (|Threads| in TLA+)
    /// - `num_resources`: Number of resources (|Resources| in TLA+)
    fn new(num_threads: usize, num_resources: usize) -> Self;

    /// Request a resource (TLA+ RequestResource)
    ///
    /// # Errors
    /// - `AlreadyOwned`: Thread already owns this resource (self-deadlock)
    /// - `DeadlockDetected`: Acquiring would create a cycle in wait-for graph
    fn request(
        &mut self,
        thread: ThreadId,
        resource: ResourceId,
    ) -> Result<RequestResult, ResourceError>;

    /// Release a resource (TLA+ ReleaseResource)
    ///
    /// # Errors
    /// - `NotOwned`: Thread doesn't own this resource
    fn release(
        &mut self,
        thread: ThreadId,
        resource: ResourceId,
    ) -> Result<(), ResourceError>;

    /// Thread finished execution (TLA+ Finish)
    ///
    /// # Errors
    /// - `ResourceLeak`: Thread still holds resources
    fn on_finish(&mut self, thread: ThreadId) -> Result<(), ResourceError>;

    /// Check if deadlock exists (TLA+ HasCycle)
    fn has_deadlock(&self) -> bool;

    /// Get deadlocked threads (TLA+ DeadlockedThreads)
    fn deadlocked_threads(&self) -> Vec<ThreadId>;

    /// Get contention score (for Ki-DPOR heuristic)
    fn contention_score(&self) -> u32;

    /// Get interleaving score (for Ki-DPOR heuristic)
    fn interleaving_score(&self) -> u32;
}

/// Result of a resource request
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RequestResult {
    /// Resource acquired immediately
    Acquired,
    
    /// Thread blocked, added to waiting queue
    Blocked,
}