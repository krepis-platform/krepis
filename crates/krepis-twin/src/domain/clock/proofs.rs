//! Kani Proofs for VirtualClock - The Zero-cost Razor Edition
//!
//! # Why This Works Now
//!
//! Previous approach (failed):
//! ```text
//! VirtualClock { Arc<Mutex<BinaryHeap>> }
//!     ↓
//! Kani: "I don't understand heap allocation!"
//!     ↓
//! Verification FAILED
//! ```
//!
//! New approach (succeeds):
//! ```text
//! VirtualClock<VerificationBackend>
//!     ↓
//! VerificationBackend { [Option<Event>; 4] }  ← Stack only!
//!     ↓
//! Kani: "I can symbolically execute this!"
//!     ↓
//! Verification PASSED
//! ```
//!
//! # TLA+ Invariant Correspondence
//! - T-001: Time Monotonicity
//! - T-002: Lamport Consistency
//! - T-003: Event Ordering

#[cfg(kani)]
mod kani_proofs {
    use super::super::*;

    /// Verify time never decreases
    ///
    /// # TLA+ Invariant
    /// ```tla
    /// TimeMonotonicity == [][virtualTimeNs' >= virtualTimeNs]_vars
    /// ```
    ///
    /// # Proof Strategy
    /// Kani explores all possible event orderings and verifies that
    /// every `tick()` operation results in time moving forward.
    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_time_monotonic() {
        let backend = VerificationBackend::new();
        let mut clock = VirtualClock::with_limits(backend, TimeMode::EventDriven, 100, 4);

        // Symbolic delays
        let delay1: u64 = kani::any();
        let delay2: u64 = kani::any();
        kani::assume(delay1 <= 50);
        kani::assume(delay2 <= 50);

        let time0 = clock.now_ns();
        
        if let Some(_) = clock.schedule(delay1, EventPayload::Test(1)) {
            if let Some(_) = clock.tick() {
                let time1 = clock.now_ns();
                kani::assert(time1 >= time0, "Time must not decrease");

                if let Some(_) = clock.schedule(delay2, EventPayload::Test(2)) {
                    if let Some(_) = clock.tick() {
                        let time2 = clock.now_ns();
                        kani::assert(time2 >= time1, "Time must remain monotonic");
                    }
                }
            }
        }
    }

    /// Verify Lamport clock increments
    ///
    /// # TLA+ Invariant
    /// ```tla
    /// LamportConsistency == [][lamportClock' >= lamportClock]_vars
    /// ```
    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_lamport_increments() {
        let backend = VerificationBackend::new();
        let mut clock = VirtualClock::with_limits(backend, TimeMode::EventDriven, 100, 4);

        let delay: u64 = kani::any();
        kani::assume(delay <= 50);

        let lamport0 = clock.lamport();
        
        if let Some(_) = clock.schedule(delay, EventPayload::Test(1)) {
            let lamport1 = clock.lamport();
            kani::assert(
                lamport1 > lamport0,
                "Lamport must increment on schedule"
            );
        }
    }

    /// Verify events fire in order
    ///
    /// # TLA+ Invariant
    /// ```tla
    /// EventOrdering == \A e1, e2 \in eventQueue :
    ///     e1.time < e2.time => ProcessedBefore(e1, e2)
    /// ```
    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_event_ordering() {
        let backend = VerificationBackend::new();
        let mut clock = VirtualClock::with_limits(backend, TimeMode::EventDriven, 100, 4);

        // Schedule two events
        kani::assume(clock.schedule(10, EventPayload::Test(1)).is_some());
        kani::assume(clock.schedule(5, EventPayload::Test(2)).is_some());

        // Earlier event fires first
        if let Some(e1) = clock.tick() {
            kani::assert(
                e1.scheduled_at_ns == 5,
                "Earlier event must fire first"
            );

            if let Some(e2) = clock.tick() {
                kani::assert(
                    e2.scheduled_at_ns >= e1.scheduled_at_ns,
                    "Events must fire in time order"
                );
            }
        }
    }

    /// Verify bounded limits enforced
    ///
    /// # TLA+ Safety Properties
    /// - Safety_TimeBound
    /// - Safety_BoundedQueue
    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_bounded_limits() {
        let backend = VerificationBackend::new();
        let mut clock = VirtualClock::with_limits(backend, TimeMode::EventDriven, 100, 2);

        // Fill queue
        kani::assume(clock.schedule(10, EventPayload::Test(1)).is_some());
        kani::assume(clock.schedule(20, EventPayload::Test(2)).is_some());

        // Exceeding limit fails
        let result = clock.schedule(30, EventPayload::Test(3));
        kani::assert(result.is_none(), "Must reject when queue full");

        // Exceeding time limit fails
        let result = clock.schedule(1000, EventPayload::Test(4));
        kani::assert(result.is_none(), "Must reject when exceeding max time");
    }
}