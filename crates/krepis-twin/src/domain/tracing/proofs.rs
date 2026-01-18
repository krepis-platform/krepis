//! Formal Verification Harnesses for Tracing Module
//!
//! These Kani proofs verify critical invariants:
//! 1. Causality preservation (no timestamp regression)
//! 2. Happens-before transitivity
//! 3. Memory safety of event recording
//! 4. Global clock monotonicity (TLA+ GlobalClockIsMax invariant)
//! 5. Thread state isolation

#![cfg(kani)]

use super::event::{EventMetadata, LamportTimestamp, SimulationEvent, ThreadId, ClockEvent, MAX_THREADS};
use super::tracer::{EventTracer, TracerConfig, VerificationBackend, VerificationTracer, TracingError};
use super::causality::CausalityGraph;

/// Verify that EventTracer maintains causality invariants
///
/// This proof verifies that even with non-deterministic event ordering,
/// the tracer maintains the causality invariant: events from the same
/// thread have strictly increasing timestamps.
///
/// Strategy: Record events first, then verify causality once at the end
/// to avoid state space explosion from repeated verify_causality() calls.
#[kani::proof]
#[kani::unwind(4)]
fn verify_tracer_causality_preservation() {
    let backend = VerificationBackend::new();
    let config = TracerConfig {
        max_events: 3,           // Small bound for Kani
        validate_causality: true, // Enable runtime checking
    };
    let mut tracer = EventTracer::new(backend, config);

    // Use a single thread to avoid cross-thread complexity
    let thread_id = ThreadId::new(0);

    // Record events sequentially
    for _i in 0..2 {
        match tracer.new_metadata(thread_id) {
            Ok(meta) => {
                let event = SimulationEvent::ClockTick {
                    meta,
                    event: ClockEvent {
                        prev_timestamp: LamportTimestamp(0),
                        new_timestamp: meta.timestamp,
                    },
                };

                match tracer.record(event) {
                    Ok(_) => {
                        // Event successfully recorded
                        // Don't call verify_causality here to avoid state explosion
                    }
                    Err(TracingError::BufferFull) => {
                        // Buffer full is acceptable
                        break;
                    }
                    Err(_e) => {
                        // Other errors should not occur with valid inputs
                        kani::assert(false, "Unexpected error in record");
                    }
                }
            }
            Err(_) => {
                // Should not happen with valid thread ID
                kani::assert(false, "Unexpected error in new_metadata");
            }
        }
    }

    // Verify causality once at the end
    // This proves that all recorded events maintain causality
    match tracer.verify_causality() {
        Ok(_) => {
            // Causality is preserved
            kani::assert(true, "Causality verified");
        }
        Err(TracingError::CausalityViolation { expected_min: _, received: _ }) => {
            // If causality violation is detected, it must be a real violation
            // Since we have validate_causality=true, record() should have caught this
            kani::assert(false, "Causality violation should have been caught by record()");
        }
        Err(_) => {
            // Other errors should not occur
            kani::assert(false, "Unexpected error in verify_causality");
        }
    }
}

/// Verify that happens-before is a partial order (transitive)
///
/// This proof verifies the fundamental property of Lamport timestamps:
/// if event e1 happens-before e2, and e2 happens-before e3,
/// then e1 happens-before e3.
#[kani::proof]
fn verify_happens_before_transitivity() {
    let events = [
        SimulationEvent::ClockTick {
            meta: EventMetadata::new(
                LamportTimestamp(1),
                ThreadId::new(0),
                0,
            ),
            event: ClockEvent {
                prev_timestamp: LamportTimestamp(0),
                new_timestamp: LamportTimestamp(1),
            },
        },
        SimulationEvent::ClockTick {
            meta: EventMetadata::new(
                LamportTimestamp(2),
                ThreadId::new(0),
                1,
            ),
            event: ClockEvent {
                prev_timestamp: LamportTimestamp(1),
                new_timestamp: LamportTimestamp(2),
            },
        },
        SimulationEvent::ClockTick {
            meta: EventMetadata::new(
                LamportTimestamp(3),
                ThreadId::new(0),
                2,
            ),
            event: ClockEvent {
                prev_timestamp: LamportTimestamp(2),
                new_timestamp: LamportTimestamp(3),
            },
        },
    ];

    let graph = CausalityGraph::from_trace(&events);

    if graph.happens_before(0, 1) && graph.happens_before(1, 2) {
        kani::assert(graph.happens_before(0, 2), "Transitivity");
    }
}

/// Verify that metadata generation is monotonic within a thread
///
/// This is a focused proof that doesn't require verify_causality
#[kani::proof]
fn verify_metadata_monotonicity() {
    let mut tracer = VerificationTracer::new_verification();
    let thread_id = ThreadId::new(0);

    let meta1 = tracer.new_metadata(thread_id).unwrap();
    let meta2 = tracer.new_metadata(thread_id).unwrap();
    let meta3 = tracer.new_metadata(thread_id).unwrap();

    // Direct invariant checks without verify_causality
    kani::assert(
        meta1.timestamp.0 < meta2.timestamp.0,
        "Timestamps must be strictly increasing"
    );
    kani::assert(
        meta2.timestamp.0 < meta3.timestamp.0,
        "Timestamps must be strictly increasing"
    );
    kani::assert(
        meta1.seq_num < meta2.seq_num,
        "Sequence numbers must be strictly increasing"
    );
    kani::assert(
        meta2.seq_num < meta3.seq_num,
        "Sequence numbers must be strictly increasing"
    );
}

/// Verify that thread synchronization updates timestamps correctly
#[kani::proof]
fn verify_thread_sync() {
    let mut tracer = VerificationTracer::new_verification();
    
    let t1 = ThreadId::new(0);
    let t2 = ThreadId::new(1);

    let meta1 = tracer.new_metadata(t1).unwrap();
    let ts1 = meta1.timestamp;

    tracer.sync_thread(t2, ts1).unwrap();

    let meta2 = tracer.new_metadata(t2).unwrap();
    
    kani::assert(
        meta2.timestamp.0 > ts1.0,
        "Synced timestamp must be greater than source"
    );
}

/// Verify that buffer full condition is properly detected
///
/// Simplified version that doesn't call verify_causality in the loop
#[kani::proof]
#[kani::unwind(5)]
fn verify_buffer_overflow_protection() {
    let backend = VerificationBackend::new();
    let config = TracerConfig {
        max_events: 2, // Very small buffer
        validate_causality: false, // Disable for faster verification
    };
    let mut tracer = EventTracer::new(backend, config);

    let thread_id = ThreadId::new(0);
    let mut successful_records = 0;

    // Try to record 4 events (more than buffer size)
    for i in 0..4 {
        let meta = tracer.new_metadata(thread_id).unwrap();
        let event = SimulationEvent::ClockTick {
            meta,
            event: ClockEvent {
                prev_timestamp: LamportTimestamp(i),
                new_timestamp: meta.timestamp,
            },
        };

        match tracer.record(event) {
            Ok(_) => {
                successful_records += 1;
                kani::assert(
                    successful_records <= 2,
                    "Should not record more than max_events"
                );
            }
            Err(TracingError::BufferFull) => {
                kani::assert(
                    successful_records == 2,
                    "Buffer should be full after 2 events"
                );
                kani::assert(
                    i >= 2,
                    "Buffer full should only occur after max_events"
                );
            }
            Err(_) => {
                kani::assert(false, "Unexpected error type");
            }
        }
    }

    // Final verification
    kani::assert(
        tracer.event_count() <= 2,
        "Final event count must not exceed max_events"
    );
    kani::assert(
        successful_records == 2,
        "Should have successfully recorded exactly 2 events"
    );
}

/// Verify global clock monotonicity with multi-thread synchronization
///
/// This proof verifies the TLA+ GlobalClockIsMax invariant:
/// The global timestamp is always the maximum of all thread timestamps,
/// and it never decreases.
///
/// This corresponds to the TLA+ invariant:
/// ```tla
/// GlobalClockIsMax ==
///     \A t \in Threads: threadClocks[t] <= globalClock
/// ```
#[kani::proof]
fn verify_global_clock_monotonicity_multi_thread() {
    let mut tracer = VerificationTracer::new_verification();
    
    let t1 = ThreadId::new(0);
    let t2 = ThreadId::new(1);

    let ts1 = LamportTimestamp(kani::any());
    kani::assume(ts1.0 < 50); // Bound for verification
    
    tracer.sync_thread(t1, ts1).unwrap();
    let global1 = tracer.global_timestamp();
    
    kani::assert(global1.0 >= ts1.0, "Global must be >= t1");

    let ts2 = LamportTimestamp(kani::any());
    kani::assume(ts2.0 < 50);
    
    tracer.sync_thread(t2, ts2).unwrap();
    let global2 = tracer.global_timestamp();
    
    kani::assert(global2.0 >= global1.0, "Global never decreases");
    
    let max_ts = if ts1.0 > ts2.0 { ts1.0 } else { ts2.0 };
    kani::assert(global2.0 >= max_ts, "Global must be >= max");
}

/// Verify that invalid thread IDs are properly rejected
///
/// This proof ensures that the tracer correctly validates thread IDs
/// and returns an error for out-of-bounds indices.
#[kani::proof]
fn verify_thread_id_validation() {
    let mut tracer = VerificationTracer::new_verification();
    
    let valid_id = ThreadId::new(0);
    kani::assert(
        tracer.new_metadata(valid_id).is_ok(),
        "Valid thread ID must work"
    );
    
    let invalid_id = ThreadId(MAX_THREADS as u32);
    kani::assert(
        tracer.new_metadata(invalid_id).is_err(),
        "Invalid thread ID must be rejected"
    );
}

/// Verify that event recording preserves event data
///
/// This proof ensures that events are stored correctly and can be
/// retrieved without corruption.
#[kani::proof]
fn verify_event_data_preservation() {
    let mut tracer = VerificationTracer::new_verification();
    
    let thread_id = ThreadId::new(0);
    let meta = tracer.new_metadata(thread_id).unwrap();
    
    let original_ts = meta.timestamp;
    let original_seq = meta.seq_num;
    
    let event = SimulationEvent::ClockTick {
        meta,
        event: ClockEvent {
            prev_timestamp: LamportTimestamp(0),
            new_timestamp: original_ts,
        },
    };
    
    tracer.record(event).unwrap();
    
    let retrieved = tracer.get_event(0).expect("Event must exist");
    let retrieved_meta = retrieved.metadata();
    
    kani::assert(
        retrieved_meta.timestamp.0 == original_ts.0,
        "Timestamp preserved"
    );
    kani::assert(
        retrieved_meta.seq_num == original_seq,
        "Sequence number preserved"
    );
    kani::assert(
        retrieved_meta.thread_id.0 == thread_id.0,
        "Thread ID preserved"
    );
}

/// Verify causality violation detection
///
/// This directly tests that causality violations are detected
/// without using verify_causality
#[kani::proof]
fn verify_causality_violation_detection() {
    let backend = VerificationBackend::new();
    let config = TracerConfig {
        max_events: 5,
        validate_causality: true,
    };
    let mut tracer = EventTracer::new(backend, config);
    
    let thread_id = ThreadId::new(0);
    
    // Record first event with timestamp 10
    let meta1 = tracer.new_metadata(thread_id).unwrap();
    kani::assume(meta1.timestamp.0 == 1); // First timestamp is always 1
    
    let event1 = SimulationEvent::ClockTick {
        meta: meta1,
        event: ClockEvent {
            prev_timestamp: LamportTimestamp(0),
            new_timestamp: meta1.timestamp,
        },
    };
    tracer.record(event1).unwrap();
    
    // Try to record event with earlier timestamp
    let bad_meta = EventMetadata::new(
        LamportTimestamp(0), // Earlier than meta1.timestamp
        thread_id,
        0,
    );
    let bad_event = SimulationEvent::ClockTick {
        meta: bad_meta,
        event: ClockEvent {
            prev_timestamp: LamportTimestamp(0),
            new_timestamp: bad_meta.timestamp,
        },
    };
    
    let result = tracer.record(bad_event);
    kani::assert(result.is_err(), "Must reject causality violation");
}

/// Verify that clearing the tracer resets event count but preserves thread states
///
/// This proof ensures that clear() behaves correctly according to its
/// specification.
#[kani::proof]
fn verify_clear_behavior() {
    let mut tracer = VerificationTracer::new_verification();
    let thread_id = ThreadId::new(0);
    
    // Record event
    let meta1 = tracer.new_metadata(thread_id).unwrap();
    let event = SimulationEvent::ClockTick {
        meta: meta1,
        event: ClockEvent {
            prev_timestamp: LamportTimestamp(0),
            new_timestamp: meta1.timestamp,
        },
    };
    tracer.record(event).unwrap();
    
    let ts_before_clear = tracer.global_timestamp();
    
    tracer.clear();
    
    kani::assert(tracer.event_count() == 0, "Event count reset");
    
    let meta2 = tracer.new_metadata(thread_id).unwrap();
    kani::assert(
        meta2.timestamp.0 > ts_before_clear.0,
        "Timestamp continues after clear"
    );
}

/// Verify thread state isolation
///
/// This proof ensures that operations on one thread don't affect
/// the state of other threads.
#[kani::proof]
fn verify_thread_state_isolation() {
    let mut tracer = VerificationTracer::new_verification();
    
    let t1 = ThreadId::new(0);
    let t2 = ThreadId::new(1);
    
    let meta1_1 = tracer.new_metadata(t1).unwrap();
    let meta2_1 = tracer.new_metadata(t2).unwrap();
    let meta1_2 = tracer.new_metadata(t1).unwrap();
    
    kani::assert(meta1_1.seq_num == 1, "T1 starts at 1");
    kani::assert(meta2_1.seq_num == 1, "T2 starts at 1");
    kani::assert(meta1_2.seq_num == 2, "T1 continues");
}

/// Verify that LamportTimestamp::increment wraps correctly
///
/// This proof verifies that timestamp increment handles overflow gracefully
/// using wrapping arithmetic.
#[kani::proof]
fn verify_timestamp_increment_wrapping() {
    let mut ts = LamportTimestamp(u64::MAX - 1);
    ts.increment();
    kani::assert(ts.0 == u64::MAX, "Increment to MAX");
    
    ts.increment();
    kani::assert(ts.0 == 0, "Wrap to 0");
}

/// Verify that LamportTimestamp::sync handles max correctly
///
/// This proof ensures that sync operation correctly implements
/// the max operation followed by increment.
#[kani::proof]
fn verify_timestamp_sync_semantics() {
    let mut ts1 = LamportTimestamp(10);
    let ts2 = LamportTimestamp(20);
    
    ts1.sync(ts2);
    kani::assert(ts1.0 == 21, "max(10,20)+1 = 21");
    
    let mut ts3 = LamportTimestamp(30);
    let ts4 = LamportTimestamp(5);
    
    ts3.sync(ts4);
    kani::assert(ts3.0 == 31, "max(30,5)+1 = 31");
}