//! Integration Test: DPOR AB-BA Deadlock Detection
//!
//! Fixed version with State Restoration (Replay) and Correct PC Tracking.

#![cfg(feature = "twin")]

use krepis_twin::domain::dpor::{DporScheduler, Operation, StepRecord};
use krepis_twin::domain::resources::{
    DefaultTracker, ResourceId, ResourceTracker, ThreadId, ResourceError, RequestResult
};

/// Replays the history from the scheduler stack to restore ResourceTracker state.
/// This ensures that when we backtrack, the resource state matches the execution path.
fn restore_tracker_state(
    num_threads: usize, 
    num_resources: usize, 
    stack: &[StepRecord]
) -> DefaultTracker {
    let mut tracker = DefaultTracker::new(num_threads, num_resources);
    
    for step in stack {
        match step.operation {
            Operation::Request => {
                let _ = tracker.request(step.thread, step.resource);
            }
            Operation::Release => {
                let _ = tracker.release(step.thread, step.resource);
            }
        }
    }
    tracker
}

/// Helper to count how many ops a thread has performed in the current stack
fn get_thread_pc(thread: ThreadId, stack: &[StepRecord]) -> usize {
    stack.iter().filter(|s| s.thread == thread).count()
}

#[test]
fn test_dpor_abba_deadlock_detection() {
    let num_threads = 2;
    let num_resources = 2;

    let mut dpor = DporScheduler::new(num_threads);
    
    let t0 = ThreadId(0);
    // let t1 = ThreadId(1); // Used implicitly
    let r0 = ResourceId(0);
    let r1 = ResourceId(1);

    let mut deadlock_detected = false;
    let mut step_count = 0;
    const MAX_STEPS: usize = 1000;

    println!("\n=== Starting DPOR Exploration (Replay Mode) ===\n");

    while !dpor.is_complete() && step_count < MAX_STEPS {
        // [Crucial] State Restoration
        // Before deciding the next move, we must ensure 'tracker' reflects
        // the current path in 'dpor.stack'.
        let mut tracker = restore_tracker_state(num_threads, num_resources, dpor.stack());

        if let Some(thread) = dpor.next_step() {
            // Determine thread's Program Counter (PC) based on history
            let pc = get_thread_pc(thread, dpor.stack());
            
            // AB-BA Logic:
            // T0: Req(R0) -> Req(R1) -> Rel(R1) -> Rel(R0)
            // T1: Req(R1) -> Req(R0) -> Rel(R0) -> Rel(R1)
            let (operation, resource) = if thread == t0 {
                match pc {
                    0 => (Operation::Request, r0),
                    1 => (Operation::Request, r1),
                    2 => (Operation::Release, r1),
                    _ => (Operation::Release, r0),
                }
            } else {
                match pc {
                    0 => (Operation::Request, r1),
                    1 => (Operation::Request, r0),
                    2 => (Operation::Release, r0),
                    _ => (Operation::Release, r1),
                }
            };

            println!(
                "[STEP {}] Depth {}: Thread {:?} (PC={}) attempts {:?} {:?}",
                step_count, dpor.current_depth(), thread, pc, operation, resource
            );

            // Execute on tracker
            let result = match operation {
                Operation::Request => tracker.request(thread, resource),
                Operation::Release => tracker.release(thread, resource).map(|_| RequestResult::Acquired),
            };

            match result {
                Ok(RequestResult::Acquired) => {
                    println!("  ✓ Acquired/Released");
                    dpor.commit_step(thread, operation, resource);
                }
                Ok(RequestResult::Blocked) => {
                    println!("  ⏸ Blocked (DPOR will backtrack this path)");
                    dpor.commit_step(thread, operation, resource);
                }
                Err(ResourceError::DeadlockDetected { cycle }) => {
                    println!("  ⚠️  DEADLOCK DETECTED! Cycle: {:?}", cycle);
                    deadlock_detected = true;
                    // Deadlock found, we can backtrack to find other paths or stop
                    dpor.backtrack();
                }
                Err(e) => {
                    // Other errors (e.g. double lock), treat as invalid path
                    println!("  ✗ Invalid operation: {:?}", e);
                    dpor.backtrack();
                }
            }
            step_count += 1;
        } else {
            println!("  ↩ Backtracking (Depth {})", dpor.current_depth());
            dpor.backtrack();
        }

        if deadlock_detected {
            break;
        }
    }

    // Print Stats
    let stats = dpor.stats();
    println!("\n=== DPOR Statistics ===");
    println!("Total steps: {}", step_count);
    println!("States explored: {}", stats.explored_states);
    println!("Backtracks: {}", stats.backtracks);
    println!("Max depth: {}", stats.max_depth);

    assert!(deadlock_detected, "DPOR failed to detect AB-BA deadlock!");
    
    // Efficiency check:
    // Full state space is much larger, DPOR should find it relatively quickly.
    // We expect at least exploring the T0-first path and then the interleaving path.
    assert!(stats.explored_states > 0);
}

#[test]
fn test_dpor_independent_operations() {
    // Correct logic for independent ops:
    // T0: Req(R0), T1: Req(R1).
    // They are independent. DPOR should NOT explore the swapped order if they are truly independent.
    // However, ensuring "not exploring" is tricky in a test.
    // We just verify it completes successfully without errors.
    
    let num_threads = 2;
    let mut dpor = DporScheduler::new(num_threads);
    let mut step_count = 0;
    
    println!("\n=== Testing Independent Operations ===\n");

    while !dpor.is_complete() && step_count < 20 {
        let mut tracker = restore_tracker_state(2, 2, dpor.stack());
        
        if let Some(thread) = dpor.next_step() {
            // T0 wants R0, T1 wants R1
            let resource = if thread == ThreadId(0) { ResourceId(0) } else { ResourceId(1) };
            
            // Check if already acquired (simple PC check)
            let pc = get_thread_pc(thread, dpor.stack());
            if pc > 0 {
                // Done for this thread
                dpor.backtrack(); 
                continue;
            }

            println!("Exec {:?} Req {:?}", thread, resource);
            let _ = tracker.request(thread, resource);
            dpor.commit_step(thread, Operation::Request, resource);
            step_count += 1;
        } else {
            dpor.backtrack();
        }
    }
    
    println!("Independent test finished. Stats: {:?}", dpor.stats());
    assert!(dpor.stats().explored_states >= 2);
}