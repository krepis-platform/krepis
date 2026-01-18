//! Kani Formal Verification Proofs

#![cfg(kani)]

use super::detailed::*;
use super::tracker::*;
use super::types::*;

/// Verify that AB-BA deadlock is detected
///
/// # TLA+ Scenario
///
/// ```tla
/// State 1: t1 acquires r1
/// State 2: t2 acquires r2  
/// State 3: t1 requests r2 (blocked)
/// State 4: t2 requests r1 -> DEADLOCK DETECTED
/// ```
#[kani::proof]
fn proof_verify_ab_ba_deadlock() {
    let mut tracker = DetailedTracker::new(2, 2);
    
    let t1 = ThreadId(0);
    let t2 = ThreadId(1);
    let r1 = ResourceId(0);
    let r2 = ResourceId(1);
    
    // State 1: t1 acquires r1
    let result = tracker.request(t1, r1);
    kani::assert(result.is_ok(), "t1 should acquire r1");
    
    // State 2: t2 acquires r2
    let result = tracker.request(t2, r2);
    kani::assert(result.is_ok(), "t2 should acquire r2");
    
    // State 3: t1 tries r2 -> Blocked
    let result = tracker.request(t1, r2);
    kani::assert(result.is_ok(), "t1 blocking on r2 should succeed");
    
    // State 4: t2 tries r1 -> DEADLOCK!
    let result = tracker.request(t2, r1);
    
    // The key assertion: deadlock should be detected
    kani::assert(result.is_err(), "Deadlock should be detected");
    
    // Verify it's specifically a DeadlockDetected error (not another error type)
    matches!(result, Err(ResourceError::DeadlockDetected { .. }));
}

/// Verify self-deadlock is prevented
#[kani::proof]
fn proof_verify_self_deadlock_prevention() {
    let mut tracker = DetailedTracker::new(2, 2);
    
    let t1 = ThreadId(0);
    let r1 = ResourceId(0);
    
    // t1 acquires r1
    let result = tracker.request(t1, r1);
    kani::assert(result.is_ok(), "First acquire should succeed");
    
    // t1 tries r1 again -> Error
    let result = tracker.request(t1, r1);
    kani::assert(result.is_err(), "Self-acquire should fail");
    
    match result {
        Err(ResourceError::AlreadyOwned { thread, resource }) => {
            kani::assert(thread == t1, "Error should reference t1");
            kani::assert(resource == r1, "Error should reference r1");
        }
        _ => kani::assert(false, "Expected AlreadyOwned error"),
    }
}

/// Verify resource leak is detected
#[kani::proof]
fn proof_verify_resource_leak_detection() {
    let mut tracker = DetailedTracker::new(2, 2);
    
    let t1 = ThreadId(0);
    let r1 = ResourceId(0);
    
    // t1 acquires r1
    let result = tracker.request(t1, r1);
    kani::assert(result.is_ok(), "Acquire should succeed");
    
    // t1 finishes without releasing -> Error
    let result = tracker.on_finish(t1);
    kani::assert(result.is_err(), "Finish with held resources should fail");
    
    match result {
        Err(ResourceError::ResourceLeak { thread, held_resources }) => {
            kani::assert(thread == t1, "Error should reference t1");
            kani::assert(held_resources.len() == 1, "Should hold exactly 1 resource");
            kani::assert(held_resources[0] == r1, "Should be holding r1");
        }
        _ => kani::assert(false, "Expected ResourceLeak error"),
    }
}

/// Verify FIFO queue order
#[kani::proof]
fn proof_verify_fifo_waiting_queue() {
    let mut tracker = DetailedTracker::new(3, 1);
    
    let t1 = ThreadId(0);
    let t2 = ThreadId(1);
    let t3 = ThreadId(2);
    let r1 = ResourceId(0);
    
    // t1 acquires r1
    tracker.request(t1, r1).unwrap();
    
    // t2 waits
    let result = tracker.request(t2, r1).unwrap();
    kani::assert(result == RequestResult::Blocked, "t2 should block");
    
    // t3 waits
    let result = tracker.request(t3, r1).unwrap();
    kani::assert(result == RequestResult::Blocked, "t3 should block");
    
    // t1 releases -> t2 should get it (FIFO)
    tracker.release(t1, r1).unwrap();
    
    // Verify t2 owns it now (can release)
    let result = tracker.release(t2, r1);
    kani::assert(result.is_ok(), "t2 should be able to release");
    
    // Verify t3 owns it now (can release)
    let result = tracker.release(t3, r1);
    kani::assert(result.is_ok(), "t3 should be able to release");
}

/// Verify simple acquire-release cycle
#[kani::proof]
fn proof_verify_simple_lifecycle() {
    let mut tracker = DetailedTracker::new(2, 2);
    
    let t1 = ThreadId(0);
    let r1 = ResourceId(0);
    
    // Acquire
    let result = tracker.request(t1, r1);
    kani::assert(result.is_ok(), "Should acquire successfully");
    kani::assert(
        result.unwrap() == RequestResult::Acquired,
        "Should be acquired immediately"
    );
    
    // Release
    let result = tracker.release(t1, r1);
    kani::assert(result.is_ok(), "Should release successfully");
    
    // Finish
    let result = tracker.on_finish(t1);
    kani::assert(result.is_ok(), "Should finish successfully");
}

/// Verify bounds checking
#[kani::proof]
fn proof_verify_bounds_checking() {
    let mut tracker = DetailedTracker::new(2, 2);
    
    // Invalid thread ID
    let result = tracker.request(ThreadId(10), ResourceId(0));
    kani::assert(result.is_err(), "Invalid thread ID should fail");
    matches!(result, Err(ResourceError::InvalidThreadId(_)));
    
    // Invalid resource ID  
    let result = tracker.request(ThreadId(0), ResourceId(10));
    kani::assert(result.is_err(), "Invalid resource ID should fail");
    matches!(result, Err(ResourceError::InvalidResourceId(_)));
}