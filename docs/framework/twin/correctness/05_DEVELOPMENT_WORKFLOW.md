# 🔄 Development Workflow Guide

**The Verification-First Development Pipeline**

```
Document: DEVELOPMENT_WORKFLOW
Version: 1.0.0
Status: Constitutional
Classification: Process Specification
```

---

## 1. Overview

This document defines the **unique development workflow** for the Krepis Digital Twin Simulator. Our workflow is distinguished by one fundamental principle:

> **"We prove correctness BEFORE we write code."**

This is not aspirational. This is mandatory.

---

## 2. The Verification-First Pipeline

### 2.1 Pipeline Overview

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  KREPIS VERIFICATION-FIRST PIPELINE                     │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐  │
│  │ PHASE 1 │──▶│ PHASE 2 │──▶│ PHASE 3 │──▶│ PHASE 4 │──▶│ PHASE 5 │  │
│  │  SPEC   │   │  TLA+   │   │  PROVE  │   │  CODE   │   │ VERIFY  │  │
│  └─────────┘   └─────────┘   └─────────┘   └─────────┘   └─────────┘  │
│       │             │             │             │             │        │
│       ▼             ▼             ▼             ▼             ▼        │
│  ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐   ┌─────────┐  │
│  │ Natural │   │ Formal  │   │   TLC   │   │  Rust   │   │  Kani   │  │
│  │Language │   │  Math   │   │  Model  │   │  Impl   │   │ Proofs  │  │
│  │  Spec   │   │  Spec   │   │  Check  │   │         │   │         │  │
│  └─────────┘   └─────────┘   └─────────┘   └─────────┘   └─────────┘  │
│                                                                         │
│  Gate:         Gate:         Gate:         Gate:         Gate:        │
│  Review        Syntax        No Errors     Compiles      All Proofs   │
│  Approved      Valid         Found         + Tests       Pass         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 Phase Transitions

Each phase has a **gate** that must be passed before proceeding:

| Phase | Gate Criteria | Blocker if Failed |
|-------|---------------|-------------------|
| 1 → 2 | Spec review approved by architect | Cannot write TLA+ |
| 2 → 3 | TLA+ syntax valid, no SANY errors | Cannot run TLC |
| 3 → 4 | TLC finds no errors (safety + liveness) | Cannot write Rust |
| 4 → 5 | Rust compiles, unit tests pass | Cannot run Kani |
| 5 → Done | All Kani proofs pass | Cannot merge |

---

## 3. Phase 1: Specification

### 3.1 Input Requirements

Every feature begins with a **natural language specification**:

```markdown
# Feature: Virtual Clock Nanosecond Precision

## Summary
Implement a virtual clock that tracks time in nanoseconds with zero drift.

## Requirements
1. Time MUST be represented as u64 nanoseconds
2. Time MUST never decrease (monotonicity)
3. Events scheduled for time T MUST fire exactly at T
4. Same-tick events MUST be ordered deterministically

## Acceptance Criteria
- [ ] TLA+ spec passes TLC with no errors
- [ ] Kani proof for monotonicity passes
- [ ] 1 billion events maintain order determinism

## Non-Goals
- Sub-nanosecond precision
- Real-time clock synchronization
```

### 3.2 Review Process

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      SPEC REVIEW WORKFLOW                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Author ──────▶ PR Created ──────▶ Architect Review                   │
│                       │                    │                            │
│                       │              ┌─────┴─────┐                      │
│                       │              ▼           ▼                      │
│                       │         Approved    Changes Requested           │
│                       │              │           │                      │
│                       │              ▼           │                      │
│                       │         Phase 2 ◀───────┘                       │
│                       │                                                 │
│   Requirements:                                                         │
│   - Clear acceptance criteria                                          │
│   - No ambiguity in requirements                                       │
│   - Edge cases identified                                              │
│   - Non-goals stated                                                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 4. Phase 2: TLA+ Specification

### 4.1 TLA+ Module Template

```tla
---------------------------- MODULE FeatureName ----------------------------
\* Feature: [Name]
\* Author: [Name]
\* Date: [Date]
\* Spec: [Link to Phase 1 spec]

EXTENDS Naturals, Sequences, TLC

\* ============================================================================
\* CONSTANTS
\* ============================================================================

CONSTANTS
    \* Define configuration parameters here

\* ============================================================================
\* VARIABLES
\* ============================================================================

VARIABLES
    \* Define state variables here

vars == << ... >>

\* ============================================================================
\* TYPE INVARIANTS
\* ============================================================================

TypeInvariant ==
    \* Define type constraints

\* ============================================================================
\* SAFETY INVARIANTS
\* ============================================================================

\* [S-XXX] Name: Description
SafetyInvariantName ==
    \* Define safety property

\* ============================================================================
\* LIVENESS PROPERTIES
\* ============================================================================

\* [L-XXX] Name: Description
LivenessPropertyName ==
    \* Define liveness property

\* ============================================================================
\* ACTIONS
\* ============================================================================

ActionName ==
    \* Define state transition

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

Init == \* Initial state
Next == \* Next state relation
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ============================================================================
\* THEOREMS
\* ============================================================================

THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariantName
THEOREM Spec => LivenessPropertyName

=============================================================================
```

### 4.2 TLA+ Writing Guidelines

| Guideline | Description | Example |
|-----------|-------------|---------|
| **Name invariants clearly** | Include ID and description | `\* [S-001] TimeMonotonicity` |
| **Use constants for bounds** | Enable different model checking configs | `CONSTANTS MaxTime` |
| **Document all actions** | Explain what each action represents | `\* ScheduleEvent: Add event to queue` |
| **Keep state minimal** | Only include necessary variables | Avoid redundant state |
| **Use type invariants** | Catch bugs early with type checking | `TypeInvariant == x \in Nat` |

---

## 5. Phase 3: TLC Model Checking

### 5.1 Running TLC

```bash
# Quick check (development)
java -jar tla2tools.jar \
  -config configs/small.cfg \
  -workers auto \
  specs/tla/FeatureName.tla

# Thorough check (pre-merge)
java -Xmx8g -jar tla2tools.jar \
  -config configs/medium.cfg \
  -workers auto \
  -deadlock \
  specs/tla/FeatureName.tla
```

### 5.2 Interpreting Results

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      TLC OUTPUT INTERPRETATION                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ✅ SUCCESS OUTPUT:                                                     │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │ Model checking completed. No error has been found.              │   │
│  │   Finished in 00h 05m 23s at (2025-01-09 10:30:45)             │   │
│  │   12345678 states generated, 1234567 distinct states found     │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│  → Proceed to Phase 4                                                  │
│                                                                         │
│  ❌ FAILURE OUTPUT:                                                     │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │ Error: Invariant TimeMonotonicity is violated.                  │   │
│  │ The following state sequence shows a violation:                 │   │
│  │                                                                 │   │
│  │ State 1: virtualTimeNs = 100                                   │   │
│  │ State 2: virtualTimeNs = 50    <-- TIME WENT BACKWARD!          │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│  → Return to Phase 2, fix TLA+ spec or requirements                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 5.3 Counter-Example Handling

When TLC finds a violation:

1. **Save the counter-example**
   ```bash
   cp MC.out artifacts/counter-examples/CE-$(date +%Y%m%d-%H%M%S).out
   ```

2. **Analyze the trace**
   - Identify which action caused the violation
   - Determine if spec bug or requirement gap

3. **Fix and re-verify**
   - Update TLA+ spec
   - Re-run TLC
   - Document the fix

---

## 6. Phase 4: Rust Implementation

### 6.1 Code Generation Guidelines

The Rust implementation must **mirror** the TLA+ specification:

```rust
// TLA+ Action:
// ScheduleEvent(delay, payload) ==
//     /\ LET newEvent == [scheduledAt |-> virtualTimeNs + delay, ...]
//        IN eventQueue' = SortedInsert(eventQueue, newEvent)
//     /\ lamportClock' = lamportClock + 1

// Rust Implementation (must match TLA+ semantics):
impl VirtualClock {
    /// Schedule a future event
    /// 
    /// # TLA+ Correspondence
    /// This implements `ScheduleEvent(delay, payload)` from VirtualClock.tla
    /// 
    /// # Invariants Maintained
    /// - EventOrdering: Events inserted in sorted order
    /// - LamportConsistency: Lamport clock incremented
    pub fn schedule(&self, delay_ns: u64, payload: EventPayload) -> u64 {
        // Corresponds to: virtualTimeNs + delay
        let scheduled_at_ns = self.now_ns() + delay_ns;
        
        // Corresponds to: lamportClock' = lamportClock + 1
        let lamport = self.lamport.fetch_add(1, Ordering::AcqRel);
        
        let event = ScheduledEvent {
            scheduled_at_ns,
            lamport,
            event_id: self.next_event_id.fetch_add(1, Ordering::Relaxed),
            payload,
        };
        
        // Corresponds to: eventQueue' = SortedInsert(eventQueue, newEvent)
        self.event_heap.lock().push(Reverse(event));
        
        event.event_id
    }
}
```

### 6.2 Code Documentation Requirements

Every function must include:

```rust
/// Brief description
/// 
/// # TLA+ Correspondence
/// References the TLA+ action this implements
/// 
/// # Invariants Maintained
/// Lists which TLA+ invariants this helps maintain
/// 
/// # Panics
/// Documents all panic conditions
/// 
/// # Examples
/// Shows usage
```

### 6.3 Unit Test Requirements

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    /// Tests for TLA+ invariant: TimeMonotonicity
    mod time_monotonicity {
        use super::*;
        
        #[test]
        fn test_tick_never_decreases_time() {
            let clock = VirtualClock::new(TimeMode::EventDriven);
            let mut prev = clock.now_ns();
            
            for _ in 0..1000 {
                clock.schedule(1, EventPayload::Test(0));
                clock.tick();
                let curr = clock.now_ns();
                assert!(curr >= prev, "Time went backward: {} -> {}", prev, curr);
                prev = curr;
            }
        }
    }
    
    /// Tests for TLA+ invariant: EventOrdering
    mod event_ordering {
        use super::*;
        
        #[test]
        fn test_same_tick_events_ordered_deterministically() {
            // ... implementation
        }
    }
}
```

---

## 6.5 Phase 4.5: Semantic Mirroring Check (MANDATORY)

Before proceeding to formal verification, every Rust implementation must pass a **Semantic Mirroring Review** that verifies 1:1 correspondence with TLA+ actions.

### 6.5.1 Mirroring Checklist

| TLA+ Element | Rust Correspondence | Verification |
|--------------|---------------------|--------------|
| Action name | Function name | Naming convention |
| Precondition | Guard clause / `if` | Logic equivalence |
| State update | Variable mutation | Order preserved |
| Postcondition | Return value / assertion | Type matching |

### 6.5.2 Automated Mirroring Tool

```bash
# Run semantic mirror check before PR
cargo run --package krepis-twin-mirror -- \
  --tla specs/tla/VirtualClock.tla \
  --rust crates/krepis-twin/src/time/virtual_clock.rs \
  --report mirror-report.md
```

### 6.5.3 Mirror Annotation Requirements

Every function implementing a TLA+ action MUST have:

```rust
/// Brief description
/// 
/// # TLA+ Correspondence
/// 
/// **Action**: `ScheduleEvent(delay, payload)` from `VirtualClock.tla:L45-L52`
/// 
/// **Precondition**: `delay > 0 /\ delay < MAX_DELAY`
/// ```tla
/// ScheduleEvent(delay, payload) ==
///     /\ delay \in 1..MaxDelay
///     /\ LET newEvent == [scheduledAt |-> virtualTimeNs + delay, ...]
/// ```
/// 
/// **State Mapping**:
/// - `virtualTimeNs` → `self.current_ns.load()`
/// - `lamportClock` → `self.lamport.fetch_add()`
/// - `eventQueue` → `self.event_heap.lock().push()`
/// 
/// # Invariants Maintained
/// - `EventOrdering` (S-003)
/// - `LamportConsistency` (S-002)
pub fn schedule(&self, delay_ns: u64, payload: EventPayload) -> u64 {
    // Implementation...
}
```

### 6.5.4 Review Gate

```
┌─────────────────────────────────────────────────────────────────────────┐
│                 PHASE 4.5 GATE: SEMANTIC MIRRORING                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  □ Every TLA+ action has corresponding Rust function                   │
│  □ All functions have `# TLA+ Correspondence` documentation            │
│  □ State mappings are explicit and complete                            │
│  □ Preconditions match TLA+ guards                                     │
│  □ Mirror tool reports 100% coverage                                   │
│  □ Peer review confirms semantic equivalence                           │
│                                                                         │
│  FAIL → Return to Phase 4, add missing documentation                   │
│  PASS → Proceed to Phase 5 (Kani Verification)                         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 7. Phase 5: Kani Verification

### 7.1 Kani Proof Structure

```rust
#[cfg(kani)]
mod proofs {
    use super::*;
    
    /// Proof: Time monotonicity
    /// 
    /// # TLA+ Invariant
    /// TimeMonotonicity == [][virtualTimeNs' >= virtualTimeNs]_vars
    /// 
    /// # Proof Strategy
    /// For any sequence of operations, verify time never decreases
    #[kani::proof]
    #[kani::unwind(10)]
    fn proof_time_monotonicity() {
        let clock = VirtualClock::new(TimeMode::EventDriven);
        
        // Arbitrary sequence of operations
        let t1 = clock.now_ns();
        
        // Schedule arbitrary event
        let delay: u64 = kani::any();
        kani::assume(delay > 0 && delay < 1_000_000);
        clock.schedule(delay, EventPayload::Test(0));
        
        // Tick
        clock.tick();
        
        let t2 = clock.now_ns();
        
        // Invariant must hold
        kani::assert(t2 >= t1, "Time monotonicity violated");
    }
    
    /// Proof: Event ordering determinism
    #[kani::proof]
    #[kani::unwind(5)]
    fn proof_event_ordering_deterministic() {
        let clock1 = VirtualClock::new(TimeMode::EventDriven);
        let clock2 = VirtualClock::new(TimeMode::EventDriven);
        
        // Same events, same schedule
        let delay: u64 = kani::any();
        kani::assume(delay > 0 && delay < 1000);
        
        clock1.schedule(delay, EventPayload::Test(1));
        clock1.schedule(delay, EventPayload::Test(2));
        
        clock2.schedule(delay, EventPayload::Test(1));
        clock2.schedule(delay, EventPayload::Test(2));
        
        // Advance both clocks
        clock1.tick();
        clock2.tick();
        let events1 = clock1.tick();
        let events2 = clock2.tick();
        
        // Order must be identical
        kani::assert(events1.len() == events2.len(), "Event count mismatch");
        
        for i in 0..events1.len() {
            kani::assert(
                events1[i].event_id == events2[i].event_id,
                "Event order not deterministic"
            );
        }
    }
    
    /// Proof: No panic on valid inputs
    #[kani::proof]
    fn proof_schedule_no_panic() {
        let clock = VirtualClock::new(TimeMode::EventDriven);
        
        let delay: u64 = kani::any();
        // Exclude overflow-causing delays
        kani::assume(delay < u64::MAX - clock.now_ns());
        
        // Should not panic
        let _id = clock.schedule(delay, EventPayload::Test(0));
    }
}
```

### 7.2 Running Kani

```bash
# Run all proofs
cd crates/krepis-twin
cargo kani --tests

# Run specific proof
cargo kani --tests --harness proof_time_monotonicity

# With verbose output
cargo kani --tests --output-format terse
```

### 7.2.1 `kani::any()` and `kani::assume()` Best Practices

**CRITICAL**: Improper use of `kani::assume()` can silently exclude valid input space, creating false confidence.

#### The Assume Pattern

```rust
// ❌ DANGEROUS: Over-constrained assumption hides bugs
#[kani::proof]
fn proof_bad_example() {
    let x: u64 = kani::any();
    kani::assume(x == 42);  // Only tests ONE value!
    assert!(process(x).is_ok());
}

// ✅ CORRECT: Minimal assumptions matching real constraints
#[kani::proof]
fn proof_good_example() {
    let x: u64 = kani::any();
    // Only assume what's ACTUALLY required by the domain
    kani::assume(x > 0);                    // Non-zero (domain requirement)
    kani::assume(x < MAX_ALLOWED);          // Within system limits
    // Do NOT assume away edge cases you want to test!
    
    assert!(process(x).is_ok());
}
```

#### Assumption Hierarchy

| Assumption Type | When to Use | Example |
|-----------------|-------------|---------|
| **Domain constraints** | Always | `x > 0` for positive values |
| **System limits** | Always | `x < u64::MAX - y` to prevent overflow |
| **API preconditions** | Carefully | Document why precondition exists |
| **Convenience** | NEVER | `x == 5` just to make proof pass |

#### Mandatory Assumption Documentation

```rust
#[kani::proof]
fn proof_with_documented_assumptions() {
    let delay: u64 = kani::any();
    
    // ASSUMPTION: delay must be non-zero
    // RATIONALE: Zero delay is handled by immediate_execute(), not schedule()
    // COVERAGE: Zero-delay case tested in proof_immediate_execute()
    kani::assume(delay > 0);
    
    // ASSUMPTION: delay must not cause overflow
    // RATIONALE: Physical constraint - cannot schedule 584+ years in future
    // COVERAGE: Overflow case tested in proof_schedule_overflow_panics()
    kani::assume(delay < u64::MAX / 2);
    
    // Now the actual proof...
}
```

#### Assumption Coverage Audit

Every PR with new Kani proofs must include:

```
## Kani Assumption Audit

| Proof | Assumptions | Rationale | Excluded Space Coverage |
|-------|-------------|-----------|-------------------------|
| proof_monotonicity | delay > 0 | API precondition | proof_zero_delay |
| proof_monotonicity | delay < MAX/2 | Overflow prevention | proof_overflow |
```

### 7.3 Interpreting Kani Results

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      KANI OUTPUT INTERPRETATION                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ✅ SUCCESS:                                                            │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │ VERIFICATION RESULT:                                            │   │
│  │   proof_time_monotonicity: SUCCESS                              │   │
│  │   proof_event_ordering: SUCCESS                                 │   │
│  │   proof_schedule_no_panic: SUCCESS                              │   │
│  │                                                                 │   │
│  │ Complete - 3 successfully verified harnesses, 0 failures        │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│  → Ready to merge                                                      │
│                                                                         │
│  ❌ FAILURE:                                                            │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │ VERIFICATION RESULT:                                            │   │
│  │   proof_time_monotonicity: FAILURE                              │   │
│  │                                                                 │   │
│  │ Assertion failed: "Time monotonicity violated"                  │   │
│  │   at crates/krepis-twin/src/time/virtual_clock.rs:150          │   │
│  │                                                                 │   │
│  │ Counter-example:                                                │   │
│  │   t1 = 100                                                      │   │
│  │   delay = 0                                                     │   │
│  │   t2 = 100  (equal, not greater)                               │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│  → Fix implementation, then re-run Kani                               │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 8. Complete Workflow Example

### 8.1 Feature: Watchdog Termination

**Phase 1: Specification**
```markdown
# Feature: Execution Watchdog

## Summary
Terminate executions that exceed their time limit.

## Requirements
1. Each tenant has a max_execution_time based on tier
2. Executions exceeding this limit MUST be terminated
3. Termination MUST happen within 150% of the limit

## Acceptance Criteria
- [ ] TLA+ WatchdogGuarantee invariant passes
- [ ] Kani proof for termination guarantee passes
- [ ] Infinite loop test terminates within limit
```

**Phase 2: TLA+ Spec**
```tla
\* [S-005] Watchdog Guarantee
WatchdogGuarantee ==
    \A t \in Tenants:
        tenantState[t].execTime > MaxExecTimeNs =>
            ~tenantState[t].active

\* Watchdog action
WatchdogTerminate(tenant) ==
    /\ tenantState[tenant].execTime > MaxExecTimeNs
    /\ tenantState' = [tenantState EXCEPT ![tenant].active = FALSE]
```

**Phase 3: TLC Check**
```bash
$ java -jar tla2tools.jar specs/tla/SovereignKernel.tla
Model checking completed. No error has been found.
```

**Phase 4: Rust Implementation**
```rust
impl ExecutionWatchdog {
    /// Terminate execution if over time limit
    /// 
    /// # TLA+ Correspondence
    /// Implements WatchdogTerminate(tenant) from SovereignKernel.tla
    /// 
    /// # Invariants Maintained
    /// - WatchdogGuarantee: Over-limit executions are terminated
    pub fn check_and_terminate(&self, tenant_id: &str) -> bool {
        let state = self.get_tenant_state(tenant_id);
        
        if state.exec_time_ns > state.max_exec_time_ns {
            self.terminate(tenant_id);
            true
        } else {
            false
        }
    }
}
```

**Phase 5: Kani Proof**
```rust
#[kani::proof]
fn proof_watchdog_terminates() {
    let watchdog = ExecutionWatchdog::new();
    
    let exec_time: u64 = kani::any();
    let max_time: u64 = kani::any();
    kani::assume(max_time > 0);
    kani::assume(exec_time > max_time);
    
    watchdog.set_tenant_state("test", TenantState {
        exec_time_ns: exec_time,
        max_exec_time_ns: max_time,
        active: true,
    });
    
    let terminated = watchdog.check_and_terminate("test");
    
    kani::assert(terminated, "Watchdog must terminate over-limit execution");
}
```

---

## 9. Git Workflow

### 9.1 Branch Naming

```
feature/[phase]-[feature-name]

Examples:
  feature/spec-virtual-clock
  feature/tla-virtual-clock  
  feature/impl-virtual-clock
```

### 9.2 Commit Messages

```
[Phase] Component: Description

Examples:
  [Spec] VirtualClock: Define nanosecond precision requirements
  [TLA+] VirtualClock: Add TimeMonotonicity invariant
  [Impl] VirtualClock: Implement tick() with monotonicity guarantee
  [Kani] VirtualClock: Add proof for time monotonicity
```

### 9.3 PR Requirements

| Phase | Required Reviewers | CI Checks |
|-------|-------------------|-----------|
| Spec | 1 Architect | None |
| TLA+ | 1 Architect | SANY syntax |
| Impl | 1 Engineer | Build, Test |
| Kani | 1 Architect | Kani proofs |

---

## 10. Quality Gates Summary

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      QUALITY GATE SUMMARY                               │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  CANNOT proceed without:                                               │
│                                                                         │
│  Phase 1 → 2: Spec approved by architect                               │
│  Phase 2 → 3: TLA+ passes SANY syntax check                            │
│  Phase 3 → 4: TLC finds no errors (quick config minimum)               │
│  Phase 4 → 4.5: Rust compiles, all unit tests pass                     │
│  Phase 4.5 → 5: Semantic mirroring check passes (TLA+ ↔ Rust 1:1)     │
│  Phase 5 → Merge: All Kani proofs pass                                 │
│                                                                         │
│  CANNOT merge without:                                                 │
│  - All phases completed (including 4.5)                                │
│  - Code coverage ≥ 80%                                                 │
│  - No clippy warnings                                                  │
│  - Documentation complete                                              │
│  - Kani assumption audit attached                                      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 11. Common Pitfalls

| Pitfall | Symptom | Solution |
|---------|---------|----------|
| **Skipping TLA+** | "I'll add spec later" | Blocked at Phase 4 gate |
| **Vague spec** | TLC state explosion | Constrain with CONSTANTS |
| **Impl ≠ Spec** | Kani failure | Trace TLA+ action correspondence |
| **Weak Kani proofs** | False confidence | Use `kani::any()` for inputs |
| **No edge cases** | Production bugs | Check EDGE_CASE_MATRIX |

---

## 12. Automated Tooling & VaaS Readiness

### 12.1 Verification-as-a-Service (VaaS) Pipeline

The Krepis platform provides **automated verification infrastructure** that issues Digital Integrity Certificates upon successful verification.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      VaaS CERTIFICATE PIPELINE                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌───────────┐   ┌───────────┐   ┌───────────┐   ┌───────────┐       │
│  │   Code    │──▶│   VaaS    │──▶│  Verify   │──▶│Certificate│       │
│  │   Push    │   │  Gateway  │   │  Engine   │   │  Issuer   │       │
│  └───────────┘   └───────────┘   └───────────┘   └───────────┘       │
│                                         │                              │
│                    ┌────────────────────┼────────────────────┐        │
│                    ▼                    ▼                    ▼        │
│              ┌──────────┐        ┌──────────┐        ┌──────────┐    │
│              │   TLC    │        │   Kani   │        │   Sim    │    │
│              │  Worker  │        │  Worker  │        │  Worker  │    │
│              └──────────┘        └──────────┘        └──────────┘    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 12.2 Digital Integrity Certificate Specification

Upon successful verification at V-Level 3+, the system issues a **Digital Integrity Certificate**:

```json
{
  "certificate_id": "DIC-2025-0109-A7B3C9D4",
  "version": "1.0",
  "issued_at": "2025-01-09T15:30:00Z",
  "expires_at": "2026-01-09T15:30:00Z",
  
  "subject": {
    "component": "krepis-twin-virtual-clock",
    "version": "1.0.0",
    "commit_hash": "a1b2c3d4e5f6..."
  },
  
  "verification_level": "V-4",
  "verification_results": {
    "tla_check": {
      "status": "PASS",
      "states_explored": 12345678,
      "invariants_verified": ["S-001", "S-002", "S-003", "L-001"],
      "duration_seconds": 3600
    },
    "kani_proofs": {
      "status": "PASS",
      "proofs_verified": 15,
      "coverage_percent": 94.5
    },
    "simulation": {
      "status": "PASS",
      "events_simulated": 1000000000,
      "edge_cases_covered": ["T-EC-001", "M-EC-006", "S-EC-010"]
    }
  },
  
  "signature": {
    "algorithm": "Ed25519",
    "public_key": "krepis-vaas-signing-key-v1",
    "value": "base64-encoded-signature..."
  },
  
  "audit_trail": {
    "ci_run_id": "gh-actions-12345",
    "reviewer": "architect@krepis.io",
    "review_timestamp": "2025-01-09T14:00:00Z"
  }
}
```

### 12.3 Certificate Verification CLI

```bash
# Verify a component has valid certificate
krepis-vaas verify \
  --component krepis-twin-virtual-clock \
  --version 1.0.0 \
  --min-level V-3

# Output:
# ✓ Certificate DIC-2025-0109-A7B3C9D4 is valid
# ✓ V-Level 4 meets minimum requirement V-3
# ✓ Signature verified against krepis-vaas-signing-key-v1
# ✓ Certificate expires in 365 days

# Embed certificate in release artifacts
krepis-vaas embed \
  --certificate DIC-2025-0109-A7B3C9D4 \
  --artifact target/release/libkrepis_twin.so \
  --output target/release/libkrepis_twin.certified.so
```

### 12.4 V-Level to Service Tier Mapping

| V-Level | Certificate Type | Service Tiers Allowed | Validity Period |
|---------|------------------|----------------------|-----------------|
| V-5 | Platinum DIC | Enterprise+ | 2 years |
| V-4 | Gold DIC | Enterprise, Pro | 1 year |
| V-3 | Silver DIC | Pro, Turbo, Standard | 6 months |
| V-2 | Bronze DIC | Standard, Free | 3 months |
| V-1 | None | Development only | N/A |

### 12.5 Automated Re-verification

Certificates automatically trigger re-verification:
- On dependency updates
- On security advisory publication
- At 75% of validity period
- On manual request

```yaml
# .github/workflows/certificate-renewal.yml
on:
  schedule:
    - cron: '0 0 * * 0'  # Weekly check
  workflow_dispatch:

jobs:
  check-certificate:
    runs-on: ubuntu-latest
    steps:
      - name: Check certificate validity
        run: |
          CERT=$(krepis-vaas check --component ${{ env.COMPONENT }})
          REMAINING=$(echo $CERT | jq '.days_remaining')
          
          if [ "$REMAINING" -lt 90 ]; then
            echo "Certificate renewal needed"
            gh workflow run verify.yml
          fi
```

---

*"The workflow is the guardian of quality."*

— K-ACA v2.0