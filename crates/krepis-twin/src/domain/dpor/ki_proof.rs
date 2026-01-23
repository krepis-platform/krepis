// crates/krepis-twin/src/domain/dpor/ki_proof.rs

//! Kani Formal Verification for Ki-DPOR State Ordering Logic
//!
//! This module provides mathematical proofs that the reverse ordering
//! implementation in `KiState` correctly transforms Rust's Max-Heap
//! (BinaryHeap) into a Min-Heap for A* search algorithm.
//!
//! # Critical Property
//! For A* to work correctly, states with LOWER priority_f values
//! must be explored FIRST. The custom Ord implementation achieves
//! this by reversing the comparison: `other.cmp(self)`.
//!
//! # Verification Strategy
//! - Use `mock_state` to construct minimal states (avoid Kani explosion)
//! - Verify mathematical properties: antisymmetry, transitivity, consistency
//! - Prove min-heap behavior: lower priority → higher rank in heap

#[cfg(kani)]
use crate::domain::dpor::KiState;
#[cfg(kani)]
use std::cmp::Ordering;

/// Constructs a minimal KiState for verification purposes.
///
/// # Design Rationale
/// KiState contains complex fields (Vec<Event>, HashMap-like structures)
/// that would cause Kani's symbolic execution to explode. We only need
/// to verify the ordering logic, which depends solely on `priority_f`.
///
/// # Fix for Compilation Error
/// We use `KiState::initial(0, 0)` to construct a valid base state
/// with empty vectors to minimize verification overhead, and then
/// inject the symbolic priority. This also bypasses the issue of
/// constructing a struct with private fields (`state_hash`).
#[cfg(kani)]
fn mock_state(priority: usize) -> KiState {
    // Create a minimal state with 0 threads and 0 resources.
    // This ensures all internal Vecs are empty, making Kani verification fast.
    let mut state = KiState::initial(0, 0);
    
    // Inject the symbolic priority we want to verify
    state.priority_f = priority;
    
    state
}

/// **Proof 1: Antisymmetry Property**
///
/// For any two states a and b:
/// - If a > b, then b < a
/// - If a == b, then b == a
///
/// Mathematical Notation: a.cmp(b) = -(b.cmp(a))
#[cfg(kani)]
#[kani::proof]
fn verify_ord_antisymmetry() {
    let p1: usize = kani::any();
    let p2: usize = kani::any();

    let s1 = mock_state(p1);
    let s2 = mock_state(p2);

    let cmp_12 = s1.cmp(&s2);
    let cmp_21 = s2.cmp(&s1);

    // Antisymmetry: a.cmp(b) must equal b.cmp(a).reverse()
    assert_eq!(cmp_12, cmp_21.reverse());
}

/// **Proof 2: Transitivity Property**
///
/// For any three states a, b, c:
/// - If a >= b AND b >= c, then a >= c
///
/// This ensures the ordering forms a valid total order.
#[cfg(kani)]
#[kani::proof]
fn verify_ord_transitivity() {
    let p1: usize = kani::any();
    let p2: usize = kani::any();
    let p3: usize = kani::any();

    let s1 = mock_state(p1);
    let s2 = mock_state(p2);
    let s3 = mock_state(p3);

    let cmp_12 = s1.cmp(&s2);
    let cmp_23 = s2.cmp(&s3);
    let cmp_13 = s1.cmp(&s3);

    // Transitivity: if a >= b and b >= c, then a >= c
    // Note: In Rust's reverse ordering for Min-Heap, "Greater" means "Higher Priority" (Lower f-value)
    // inside the heap logic, but strictly speaking, `cmp` returns the ordering relative to sort order.
    
    // Check strict transitivity for "Greater" (which means s1 is processed BEFORE s2)
    if matches!(cmp_12, Ordering::Greater | Ordering::Equal)
        && matches!(cmp_23, Ordering::Greater | Ordering::Equal)
    {
        assert!(matches!(cmp_13, Ordering::Greater | Ordering::Equal));
    }

    // Check strict transitivity for "Less"
    if matches!(cmp_12, Ordering::Less | Ordering::Equal)
        && matches!(cmp_23, Ordering::Less | Ordering::Equal)
    {
        assert!(matches!(cmp_13, Ordering::Less | Ordering::Equal));
    }
}

/// **Proof 3: Consistency Between Ord and PartialOrd**
///
/// Verifies that `partial_cmp` always returns `Some(cmp)`.
/// This is required by Rust's trait contract for total orders.
#[cfg(kani)]
#[kani::proof]
fn verify_ord_consistency() {
    let p1: usize = kani::any();
    let p2: usize = kani::any();

    let s1 = mock_state(p1);
    let s2 = mock_state(p2);

    let ord_result = s1.cmp(&s2);
    let partial_result = s1.partial_cmp(&s2);

    // PartialOrd must return Some(Ord result) for total orders
    assert_eq!(partial_result, Some(ord_result));
}

/// **Proof 4: Min-Heap Behavior (CRITICAL FOR A*)**
///
/// Verifies that states with LOWER priority values are "greater"
/// in the ordering, so they are popped first from BinaryHeap.
///
/// # A* Search Requirement
/// In A* algorithm, f(n) = g(n) + h(n) represents the estimated
/// total cost. States with LOWER f-values should be explored FIRST.
///
/// # Implementation
/// BinaryHeap is a Max-Heap, so we need:
/// - Lower priority value (e.g., 10) → "Greater" ordering → Top of Heap
/// - Higher priority value (e.g., 20) → "Less" ordering → Bottom of Heap
///
/// This is achieved by `other.cmp(self)` (reversed comparison).
#[cfg(kani)]
#[kani::proof]
fn verify_min_heap_logic() {
    let p_low: usize = kani::any();
    let p_high: usize = kani::any();

    // Assume p_low is strictly less than p_high (e.g., 10 vs 20)
    kani::assume(p_low < p_high);

    let s_low = mock_state(p_low);
    let s_high = mock_state(p_high);

    // CRITICAL ASSERTION:
    // We want s_low to be at the TOP of the Max-Heap.
    // So s_low must compare as GREATER than s_high.
    assert_eq!(s_low.cmp(&s_high), Ordering::Greater);

    // Verify reverse direction for completeness
    assert_eq!(s_high.cmp(&s_low), Ordering::Less);

    // Verify that equal priorities produce Equal ordering
    let p_same: usize = kani::any();
    let s_same1 = mock_state(p_same);
    let s_same2 = mock_state(p_same);
    assert_eq!(s_same1.cmp(&s_same2), Ordering::Equal);
}

/// **Proof 5: Bounded Priority Verification**
///
/// Verifies ordering behavior for edge cases:
/// - Minimum priority (0)
/// - Maximum priority (usize::MAX)
/// - Adjacent priorities (n and n+1)
#[cfg(kani)]
#[kani::proof]
fn verify_bounded_priorities() {
    // Edge case 1: Minimum priority (0) is the "Best" priority.
    // It should be Greater than any higher value (e.g., 100).
    let s_min = mock_state(0);
    let s_mid = mock_state(100);
    assert_eq!(s_min.cmp(&s_mid), Ordering::Greater);

    // Edge case 2: Maximum priority (usize::MAX) is the "Worst" priority.
    // It should be Less than any lower value.
    let s_max = mock_state(usize::MAX);
    assert_eq!(s_max.cmp(&s_mid), Ordering::Less);

    // Edge case 3: Adjacent priorities
    let p: usize = kani::any();
    kani::assume(p < usize::MAX); // Avoid overflow

    let s_n = mock_state(p);
    let s_n_plus_1 = mock_state(p + 1);

    // Lower value (p) > Higher value (p+1) in ordering
    assert_eq!(s_n.cmp(&s_n_plus_1), Ordering::Greater);
    assert_eq!(s_n_plus_1.cmp(&s_n), Ordering::Less);
}