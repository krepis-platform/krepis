//! Classic DPOR Benchmark Suite
//!
//! This benchmark establishes a baseline for the Classic DPOR implementation
//! to compare against the future Ki-DPOR (Krepis Intelligent DPOR).
//!
//! # Scenarios
//!
//! 1. **AB-BA Deadlock**: Small-scale (2 threads, 2 resources)
//!    - Tests basic deadlock detection
//!    - Measures overhead of backtracking
//!
//! 2. **Dining Philosophers**: Scalability stress test
//!    - N philosophers, N forks
//!    - Demonstrates exponential state explosion
//!    - Justifies need for Ki-DPOR optimization

#![cfg(feature = "twin")]

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use krepis_twin::domain::dpor::{DporScheduler, Operation, StepRecord};
use krepis_twin::domain::resources::{
    DefaultTracker as ResourceTracker, ResourceId, ResourceTracker as ResourceTrackerTrait,
    ThreadId, ResourceError, RequestResult,
};

// ============================================================================
// Helper Functions
// ============================================================================

/// Restore ResourceTracker state from scheduler stack
///
/// This replays the entire execution history to bring the tracker
/// to the correct state after backtracking.
fn restore_tracker_state(
    num_threads: usize,
    num_resources: usize,
    stack: &[StepRecord],
) -> ResourceTracker {
    let mut tracker = ResourceTracker::new(num_threads, num_resources);

    for step in stack {
        let _ = match step.operation {
            Operation::Request => tracker.request(step.thread, step.resource),
            Operation::Release => tracker.release(step.thread, step.resource).map(|_| RequestResult::Acquired),
        };
    }

    tracker
}

/// Get thread's program counter (number of steps executed)
fn get_thread_pc(thread: ThreadId, stack: &[StepRecord]) -> usize {
    stack.iter().filter(|s| s.thread == thread).count()
}

/// Run a complete DPOR exploration
///
/// Returns (explored_states, backtracks, deadlock_found)
fn run_exploration<F>(
    mut dpor: DporScheduler,
    num_threads: usize,
    num_resources: usize,
    mut get_operation: F,
    max_steps: usize,
) -> (usize, usize, bool)
where
    F: FnMut(ThreadId, usize) -> Option<(Operation, ResourceId)>,
{
    let mut deadlock_found = false;
    let mut step_count = 0;

    while !dpor.is_complete() && step_count < max_steps {
        // Restore state
        let mut tracker = restore_tracker_state(num_threads, num_resources, dpor.stack());

        if let Some(thread) = dpor.next_step() {
            let pc = get_thread_pc(thread, dpor.stack());

            // Get operation from scenario
            if let Some((operation, resource)) = get_operation(thread, pc) {
                // Execute on tracker
                let result = match operation {
                    Operation::Request => tracker.request(thread, resource),
                    Operation::Release => tracker.release(thread, resource).map(|_| RequestResult::Acquired),
                };

                match result {
                    Ok(RequestResult::Acquired) | Ok(RequestResult::Blocked) => {
                        dpor.commit_step(thread, operation, resource);
                    }
                    Err(ResourceError::DeadlockDetected { .. }) => {
                        deadlock_found = true;
                        dpor.backtrack();
                    }
                    Err(_) => {
                        dpor.backtrack();
                    }
                }
            } else {
                // No more operations for this thread
                dpor.backtrack();
            }

            step_count += 1;
        } else {
            // Backtrack
            dpor.backtrack();
        }
    }

    let stats = dpor.stats();
    (stats.explored_states, stats.backtracks, deadlock_found)
}

// ============================================================================
// Scenario 1: AB-BA Deadlock
// ============================================================================

/// AB-BA Deadlock scenario
///
/// # Setup
/// - 2 threads, 2 resources
/// - T0: Request(R0) -> Request(R1)
/// - T1: Request(R1) -> Request(R0) -> DEADLOCK
///
/// # Expected
/// - Deadlock detected
/// - ~4-6 states explored
fn abba_deadlock_operation(thread: ThreadId, pc: usize) -> Option<(Operation, ResourceId)> {
    let t0 = ThreadId(0);
    let r0 = ResourceId(0);
    let r1 = ResourceId(1);

    if thread == t0 {
        match pc {
            0 => Some((Operation::Request, r0)),
            1 => Some((Operation::Request, r1)),
            2 => Some((Operation::Release, r1)),
            3 => Some((Operation::Release, r0)),
            _ => None,
        }
    } else {
        // T1
        match pc {
            0 => Some((Operation::Request, r1)),
            1 => Some((Operation::Request, r0)),
            2 => Some((Operation::Release, r0)),
            3 => Some((Operation::Release, r1)),
            _ => None,
        }
    }
}

fn bench_abba_deadlock(c: &mut Criterion) {
    c.bench_function("dpor_abba_deadlock", |b| {
        b.iter(|| {
            let dpor = DporScheduler::new(2);
            let (states, backtracks, deadlock) = run_exploration(
                dpor,
                2,
                2,
                abba_deadlock_operation,
                100,
            );

            // Verify correctness
            assert!(deadlock, "Should detect deadlock");

            black_box((states, backtracks))
        });
    });
}

// ============================================================================
// Scenario 2: Dining Philosophers
// ============================================================================

/// Dining Philosophers scenario
///
/// # Setup
/// - N philosophers, N forks (resources)
/// - Each philosopher `i` tries to acquire:
///   1. Fork `i` (left)
///   2. Fork `(i+1) % N` (right)
/// - Classic deadlock: all grab left fork, then wait for right
///
/// # Scalability
/// - N=3: ~27 states (manageable)
/// - N=4: ~256 states (exponential growth!)
/// - N=5: ~3125 states (too slow for baseline)
fn dining_philosophers_operation(
    n: usize,
) -> impl FnMut(ThreadId, usize) -> Option<(Operation, ResourceId)> {
    move |thread: ThreadId, pc: usize| {
        let i = thread.as_usize();
        let left_fork = ResourceId(i);
        let right_fork = ResourceId((i + 1) % n);

        match pc {
            0 => Some((Operation::Request, left_fork)),
            1 => Some((Operation::Request, right_fork)),
            2 => Some((Operation::Release, right_fork)),
            3 => Some((Operation::Release, left_fork)),
            _ => None,
        }
    }
}

fn bench_dining_philosophers(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpor_dining_philosophers");

    for n in [3, 4].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(n), n, |b, &n| {
            b.iter(|| {
                let dpor = DporScheduler::new(n);
                let (states, backtracks, _) = run_exploration(
                    dpor,
                    n,
                    n,
                    dining_philosophers_operation(n),
                    10000, // Higher limit for larger N
                );

                black_box((states, backtracks))
            });
        });
    }

    group.finish();
}

// ============================================================================
// Scenario 3: Independent Operations (Best Case)
// ============================================================================

/// Independent operations scenario (best case for DPOR)
///
/// # Setup
/// - N threads, N resources
/// - Each thread only accesses its own resource
/// - No conflicts -> minimal backtracking
///
/// # Expected
/// - ~N states explored
/// - Minimal backtracks
/// - Demonstrates DPOR's efficiency on independent ops
fn independent_operations(n: usize) -> impl FnMut(ThreadId, usize) -> Option<(Operation, ResourceId)> {
    move |thread: ThreadId, pc: usize| {
        let resource = ResourceId(thread.as_usize());

        match pc {
            0 => Some((Operation::Request, resource)),
            1 => Some((Operation::Release, resource)),
            _ => None,
        }
    }
}

fn bench_independent_operations(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpor_independent_ops");

    for n in [2, 4, 8].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(n), n, |b, &n| {
            b.iter(|| {
                let dpor = DporScheduler::new(n);
                let (states, backtracks, _) = run_exploration(
                    dpor,
                    n,
                    n,
                    independent_operations(n),
                    1000,
                );

                black_box((states, backtracks))
            });
        });
    }

    group.finish();
}

// ============================================================================
// Scenario 4: Sequential Bottleneck (Worst Case)
// ============================================================================

/// Sequential bottleneck scenario (worst case for any DPOR)
///
/// # Setup
/// - N threads, 1 shared resource
/// - All threads compete for the same resource
/// - Maximum contention
///
/// # Expected
/// - N! possible interleavings
/// - Heavy backtracking
/// - Demonstrates state explosion
fn sequential_bottleneck(n: usize) -> impl FnMut(ThreadId, usize) -> Option<(Operation, ResourceId)> {
    move |_thread: ThreadId, pc: usize| {
        let shared_resource = ResourceId(0);

        match pc {
            0 => Some((Operation::Request, shared_resource)),
            1 => Some((Operation::Release, shared_resource)),
            _ => None,
        }
    }
}

fn bench_sequential_bottleneck(c: &mut Criterion) {
    let mut group = c.benchmark_group("dpor_sequential_bottleneck");

    for n in [2, 3, 4].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(n), n, |b, &n| {
            b.iter(|| {
                let dpor = DporScheduler::new(n);
                let (states, backtracks, _) = run_exploration(
                    dpor,
                    n,
                    1, // Single shared resource
                    sequential_bottleneck(n),
                    5000,
                );

                black_box((states, backtracks))
            });
        });
    }

    group.finish();
}

// ============================================================================
// Criterion Configuration
// ============================================================================

criterion_group!(
    benches,
    bench_abba_deadlock,
    bench_dining_philosophers,
    bench_independent_operations,
    bench_sequential_bottleneck
);

criterion_main!(benches);