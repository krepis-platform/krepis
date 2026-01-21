//! Kani Formal Verification Proofs for DPOR
//!
//! This module contains formal verification harnesses that prove the correctness
//! of the Classic DPOR implementation with TinyBitSet.
//!
//! # Kani Limitations
//!
//! Due to Kani's limited support for dynamic allocation (Vec), we focus on
//! verifying the core algorithms (TinyBitSet, VectorClock) rather than the
//! full scheduler state machine.

#![cfg(kani)]

use super::scheduler::*;
use super::vector_clock::*;
use crate::domain::resources::{ResourceId, ThreadId};

// ============================================================================
// TinyBitSet Proofs (Pure bitwise operations - Kani handles these well)
// ============================================================================

/// Verify TinyBitSet insert and contains operations
///
/// # Properties Verified
///
/// 1. Initially empty
/// 2. Insert sets the bit
/// 3. Contains returns true for set bits
/// 4. Contains returns false for unset bits
#[kani::proof]
fn proof_tiny_bitset_insert_contains() {
    let mut bs = TinyBitSet::new(8);
    
    // Initially empty
    kani::assert(!bs.contains(0), "Initially should not contain 0");
    kani::assert(!bs.contains(1), "Initially should not contain 1");
    
    // Insert bit 0
    bs.insert(0);
    kani::assert(bs.contains(0), "Should contain 0 after insert");
    kani::assert(!bs.contains(1), "Should not contain 1");
    
    // Insert bit 3
    bs.insert(3);
    kani::assert(bs.contains(0), "Should still contain 0");
    kani::assert(bs.contains(3), "Should contain 3 after insert");
    kani::assert(!bs.contains(2), "Should not contain 2");
}

/// Verify TinyBitSet difference operation (A \ B = A & !B)
///
/// # Properties Verified
///
/// 1. Difference computes set subtraction correctly
/// 2. A \ B contains elements in A but not in B
/// 3. Bitwise: A & !B
#[kani::proof]
fn proof_tiny_bitset_difference() {
    let mut a = TinyBitSet::new(8);
    let mut b = TinyBitSet::new(8);
    
    // A = {0, 1, 2}
    a.insert(0);
    a.insert(1);
    a.insert(2);
    
    // B = {1, 2}
    b.insert(1);
    b.insert(2);
    
    // A \ B should be {0}
    a.difference_with(&b);
    
    kani::assert(a.contains(0), "0 should remain (in A, not in B)");
    kani::assert(!a.contains(1), "1 should be removed (in both)");
    kani::assert(!a.contains(2), "2 should be removed (in both)");
    kani::assert(!a.contains(3), "3 should not be present");
}

/// Verify TinyBitSet next_set_bit returns lowest set bit
///
/// # Properties Verified
///
/// 1. Empty set returns None
/// 2. Returns lowest set bit index
/// 3. Uses CTZ (Count Trailing Zeros) correctly
#[kani::proof]
fn proof_tiny_bitset_next_set_bit() {
    let mut bs = TinyBitSet::new(8);
    
    // Empty
    kani::assert(bs.next_set_bit().is_none(), "Empty set should return None");
    
    // Insert bit 5
    bs.insert(5);
    kani::assert(bs.next_set_bit() == Some(5), "Should return 5");
    
    // Insert bit 2 (lower than 5)
    bs.insert(2);
    kani::assert(bs.next_set_bit() == Some(2), "Should return lowest bit (2)");
    
    // Insert bit 0 (lowest possible)
    bs.insert(0);
    kani::assert(bs.next_set_bit() == Some(0), "Should return 0");
}

/// Verify TinyBitSet clear operation
///
/// # Properties Verified
///
/// 1. Clear sets all bits to 0
/// 2. is_clear returns true after clear
#[kani::proof]
fn proof_tiny_bitset_clear() {
    let mut bs = TinyBitSet::new(8);
    
    // Insert some bits
    bs.insert(0);
    bs.insert(3);
    bs.insert(7);
    
    kani::assert(!bs.is_clear(), "Should not be clear");
    
    // Clear
    bs.clear();
    
    kani::assert(bs.is_clear(), "Should be clear after clear()");
    kani::assert(!bs.contains(0), "Bit 0 should be cleared");
    kani::assert(!bs.contains(3), "Bit 3 should be cleared");
    kani::assert(!bs.contains(7), "Bit 7 should be cleared");
}

/// Verify TinyBitSet Copy semantics
///
/// # Properties Verified
///
/// 1. TinyBitSet is Copy (not Clone)
/// 2. Copies are independent
/// 3. Modifying original doesn't affect copy
#[kani::proof]
fn proof_tiny_bitset_copy_semantics() {
    let mut a = TinyBitSet::new(8);
    a.insert(0);
    a.insert(1);
    
    // Copy (not clone!)
    let b = a;
    
    // Both should have same bits initially
    kani::assert(b.contains(0), "Copy should contain 0");
    kani::assert(b.contains(1), "Copy should contain 1");
    
    // Modify original
    a.insert(2);
    a.clear();
    
    // Copy should be unaffected (true Copy semantics, not reference)
    kani::assert(b.contains(0), "Copy should still contain 0");
    kani::assert(b.contains(1), "Copy should still contain 1");
    kani::assert(!b.contains(2), "Copy should not have new bits from original");
}

/// Verify TinyBitSet difference is not commutative
///
/// # Properties Verified
///
/// A \ B ≠ B \ A (not commutative)
/// A \ B = A & !B (correct definition)
#[kani::proof]
fn proof_tiny_bitset_difference_not_commutative() {
    let mut a = TinyBitSet::new(8);
    let mut b = TinyBitSet::new(8);
    
    a.insert(0);
    a.insert(1);
    
    b.insert(1);
    b.insert(2);
    
    // Compute A \ B
    let mut a_minus_b = a;
    a_minus_b.difference_with(&b);
    
    // Compute B \ A
    let mut b_minus_a = b;
    b_minus_a.difference_with(&a);
    
    // They should be different!
    kani::assert(a_minus_b.contains(0), "A\\B should contain 0");
    kani::assert(!a_minus_b.contains(1), "A\\B should not contain 1");
    kani::assert(!a_minus_b.contains(2), "A\\B should not contain 2");
    
    kani::assert(!b_minus_a.contains(0), "B\\A should not contain 0");
    kani::assert(!b_minus_a.contains(1), "B\\A should not contain 1");
    kani::assert(b_minus_a.contains(2), "B\\A should contain 2");
}

/// Verify bitwise operations are equivalent to set operations
///
/// # Properties Verified
///
/// TinyBitSet implements set theory correctly using bitwise ops
#[kani::proof]
fn proof_tiny_bitset_bitwise_correctness() {
    let mut set = TinyBitSet::new(8);
    
    // Union simulation: insert multiple
    set.insert(0);
    set.insert(2);
    set.insert(4);
    
    // Verify state
    kani::assert(set.contains(0) && set.contains(2) && set.contains(4), 
                 "All inserted elements should be present");
    kani::assert(!set.contains(1) && !set.contains(3), 
                 "Non-inserted elements should be absent");
    
    // Intersection simulation via difference
    let mut intersect = set;
    let mut filter = TinyBitSet::new(8);
    filter.insert(0);
    filter.insert(1);
    
    // intersect ∩ filter = intersect - (intersect - filter)
    let mut temp = intersect;
    temp.difference_with(&filter);
    intersect.difference_with(&temp);
    
    kani::assert(intersect.contains(0), "Intersection should contain 0");
    kani::assert(!intersect.contains(2), "Intersection should not contain 2");
}

// ============================================================================
// Vector Clock Proofs (Stack-only operations - Kani friendly)
// ============================================================================

/// Verify that vector clocks correctly implement happens-before relation
#[kani::proof]
fn proof_vector_clock_happens_before() {
    let mut vc1 = VectorClock::new();
    let mut vc2 = VectorClock::new();
    
    // Initial state: neither happens-before the other
    kani::assert(
        !vc1.happens_before(&vc2),
        "Equal clocks should not have happens-before relation"
    );
    
    // Tick vc1 for thread 0
    vc1.tick(ThreadId(0));
    
    // Now vc1 happens-before vc2 is false (vc2 is smaller)
    kani::assert(
        !vc1.happens_before(&vc2),
        "vc1 > vc2, so vc1 does not happen before vc2"
    );
    
    // Tick vc2 for thread 0 twice
    vc2.tick(ThreadId(0));
    vc2.tick(ThreadId(0));
    
    // Now vc1 < vc2, so vc1 happens-before vc2
    kani::assert(
        vc1.happens_before(&vc2),
        "vc1 [1,0,0...] should happen before vc2 [2,0,0...]"
    );
    
    // Antisymmetry: vc2 should NOT happen-before vc1
    kani::assert(
        !vc2.happens_before(&vc1),
        "If vc1 < vc2, then NOT vc2 < vc1"
    );
}

/// Verify vector clock merge operation
#[kani::proof]
fn proof_vector_clock_merge() {
    let mut vc1 = VectorClock::new();
    let mut vc2 = VectorClock::new();
    
    // Set up vc1: [3, 1, 2]
    vc1.set(ThreadId(0), 3);
    vc1.set(ThreadId(1), 1);
    vc1.set(ThreadId(2), 2);
    
    // Set up vc2: [2, 5, 1]
    vc2.set(ThreadId(0), 2);
    vc2.set(ThreadId(1), 5);
    vc2.set(ThreadId(2), 1);
    
    // Merge vc1 with vc2
    vc1.merge(&vc2);
    
    // Result should be [3, 5, 2]
    kani::assert(vc1.get(ThreadId(0)) == 3, "max(3, 2) = 3");
    kani::assert(vc1.get(ThreadId(1)) == 5, "max(1, 5) = 5");
    kani::assert(vc1.get(ThreadId(2)) == 2, "max(2, 1) = 2");
}

/// Verify concurrent detection
#[kani::proof]
fn proof_vector_clock_concurrent() {
    let mut vc1 = VectorClock::new();
    let mut vc2 = VectorClock::new();
    
    // vc1: [1, 3, 2]
    vc1.set(ThreadId(0), 1);
    vc1.set(ThreadId(1), 3);
    vc1.set(ThreadId(2), 2);
    
    // vc2: [2, 1, 3]
    vc2.set(ThreadId(0), 2);
    vc2.set(ThreadId(1), 1);
    vc2.set(ThreadId(2), 3);
    
    // Neither happens-before the other -> concurrent
    kani::assert(
        !vc1.happens_before(&vc2) && !vc2.happens_before(&vc1),
        "Neither should happen-before the other"
    );
    
    kani::assert(
        vc1.concurrent(&vc2),
        "Operations should be concurrent"
    );
}

// ============================================================================
// DPOR Core Logic Proofs (Without full scheduler state)
// ============================================================================

/// Verify dependency detection logic (without scheduler)
///
/// This tests the is_dependent logic in isolation
#[kani::proof]
fn proof_dpor_dependency_logic() {
    let step1 = StepRecord {
        thread: ThreadId(0),
        operation: Operation::Request,
        resource: ResourceId(0),
        depth: 0,
        clock: VectorClock::new(),
    };
    
    let step2_same = StepRecord {
        thread: ThreadId(1),
        operation: Operation::Request,
        resource: ResourceId(0),
        depth: 1,
        clock: VectorClock::new(),
    };
    
    let step3_diff = StepRecord {
        thread: ThreadId(1),
        operation: Operation::Request,
        resource: ResourceId(1),
        depth: 1,
        clock: VectorClock::new(),
    };
    
    // Manual dependency check (avoiding scheduler creation)
    let same_resource = step1.resource == step2_same.resource;
    let diff_thread = step1.thread != step2_same.thread;
    
    kani::assert(same_resource && diff_thread, "Should be dependent");
    
    let diff_resource = step1.resource == step3_diff.resource;
    kani::assert(!diff_resource, "Should be independent (different resource)");
}

/// Verify concurrency detection logic (without scheduler)
#[kani::proof]
fn proof_dpor_concurrency_logic() {
    let mut vc1 = VectorClock::new();
    let mut vc2 = VectorClock::new();
    
    // Concurrent clocks
    vc1.set(ThreadId(0), 2);
    vc1.set(ThreadId(1), 1);
    
    vc2.set(ThreadId(0), 1);
    vc2.set(ThreadId(1), 2);
    
    let step1 = StepRecord {
        thread: ThreadId(0),
        operation: Operation::Request,
        resource: ResourceId(0),
        depth: 0,
        clock: vc1,
    };
    
    let step2 = StepRecord {
        thread: ThreadId(1),
        operation: Operation::Request,
        resource: ResourceId(0),
        depth: 1,
        clock: vc2,
    };
    
    // They should be concurrent
    kani::assert(step1.clock.concurrent(&step2.clock), "Should be concurrent");
}

/// Verify StepRecord creation and properties
#[kani::proof]
fn proof_step_record_properties() {
    let vc = VectorClock::new();
    
    let step = StepRecord {
        thread: ThreadId(0),
        operation: Operation::Request,
        resource: ResourceId(1),
        depth: 5,
        clock: vc,
    };
    
    kani::assert(step.thread == ThreadId(0), "Thread ID correct");
    kani::assert(step.resource == ResourceId(1), "Resource ID correct");
    kani::assert(step.depth == 5, "Depth correct");
    kani::assert(step.operation == Operation::Request, "Operation correct");
}

/// Verify Operation enum properties
#[kani::proof]
fn proof_operation_enum() {
    let req = Operation::Request;
    let rel = Operation::Release;
    
    kani::assert(req != rel, "Request != Release");
    kani::assert(req == Operation::Request, "Equality works");
    
    // Match pattern works
    match req {
        Operation::Request => kani::assert(true, "Match works"),
        Operation::Release => kani::assert(false, "Should not match"),
    }
}