//! NoOpTracker - Zero-Cost Production Implementation

use super::tracker::*;
use super::types::*;

/// Production tracker with zero runtime cost
///
/// # Zero-Cost Guarantee
///
/// All methods are:
/// - `#[inline(always)]`: Force inlining
/// - Empty body: No operations
/// - Trivial return values
///
/// The compiler will completely optimize away all calls to this tracker.
///
/// # Example
///
/// ```rust,ignore
/// let mut tracker = NoOpTracker::new(8, 4);
/// tracker.request(ThreadId(0), ResourceId(0))?;
/// // Compiled code: NOTHING (removed by optimizer)
/// ```
pub struct NoOpTracker;

impl ResourceTracker for NoOpTracker {
    #[inline(always)]
    fn new(_num_threads: usize, _num_resources: usize) -> Self {
        Self
    }

    #[inline(always)]
    fn request(
        &mut self,
        _thread: ThreadId,
        _resource: ResourceId,
    ) -> Result<RequestResult, ResourceError> {
        Ok(RequestResult::Acquired)
    }

    #[inline(always)]
    fn release(
        &mut self,
        _thread: ThreadId,
        _resource: ResourceId,
    ) -> Result<(), ResourceError> {
        Ok(())
    }

    #[inline(always)]
    fn on_finish(&mut self, _thread: ThreadId) -> Result<(), ResourceError> {
        Ok(())
    }

    #[inline(always)]
    fn has_deadlock(&self) -> bool {
        false
    }

    #[inline(always)]
    fn deadlocked_threads(&self) -> Vec<ThreadId> {
        Vec::new()
    }

    #[inline(always)]
    fn contention_score(&self) -> u32 {
        0
    }

    #[inline(always)]
    fn interleaving_score(&self) -> u32 {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_noop_compiles() {
        let mut tracker = NoOpTracker::new(8, 4);
        
        // All operations should succeed with no side effects
        assert_eq!(
            tracker.request(ThreadId(0), ResourceId(0)).unwrap(),
            RequestResult::Acquired
        );
        
        tracker.release(ThreadId(0), ResourceId(0)).unwrap();
        tracker.on_finish(ThreadId(0)).unwrap();
        
        assert!(!tracker.has_deadlock());
        assert_eq!(tracker.deadlocked_threads().len(), 0);
    }
}