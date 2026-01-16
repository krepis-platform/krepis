# 🔬 TLA+ Verification Strategy

**Formal Methods Integration for Krepis Digital Twin Simulator**

```
Document: TLA_VERIFICATION_STRATEGY
Version: 1.0.0
Status: Constitutional
Classification: Formal Verification Specification
```

---

## 1. Overview

This document defines the strategy for integrating TLA+ formal verification into the Krepis Digital Twin Simulator development lifecycle. TLA+ serves as the **mathematical foundation** that proves our simulator's correctness before implementation.

---

## 2. Verification Philosophy

### 2.1 The Formal-First Principle

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    FORMAL-FIRST DEVELOPMENT FLOW                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌───────────┐     ┌───────────┐     ┌───────────┐     ┌───────────┐ │
│   │           │     │           │     │           │     │           │ │
│   │   Spec    │────▶│   TLA+    │────▶│    TLC    │────▶│   Code    │ │
│   │           │     │   Model   │     │   Check   │     │   Gen     │ │
│   │           │     │           │     │           │     │           │ │
│   └───────────┘     └───────────┘     └───────────┘     └───────────┘ │
│        │                 │                 │                 │         │
│        │                 │                 │                 │         │
│        ▼                 ▼                 ▼                 ▼         │
│   Human writes      Precise math      Model checker      Rust impl    │
│   requirements      specification     finds bugs         with Kani    │
│                                                                         │
│   "We prove BEFORE we code, not after."                                │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 2.2 What TLA+ Verifies

| Property Type | Description | Example |
|---------------|-------------|---------|
| **Safety** | Bad things never happen | Time never goes backward |
| **Liveness** | Good things eventually happen | Runnable tasks eventually run |
| **Invariants** | Properties that always hold | Heap usage ≤ limit |
| **Refinement** | Abstract spec matches concrete | High-level → implementation |

---

## 3. TLA+ Module Structure

### 3.1 Module Hierarchy

```
specs/tla/
├── KrepisUniverse.tla          # Top-level specification
├── modules/
│   ├── VirtualClock.tla        # Time module
│   ├── SimulatedMemory.tla     # Memory module
│   ├── SchedulerOracle.tla     # Scheduler module
│   └── SovereignKernel.tla     # Kernel module
├── properties/
│   ├── Safety.tla              # All safety properties
│   ├── Liveness.tla            # All liveness properties
│   └── Refinement.tla          # Refinement mappings
└── configs/
    ├── small.cfg               # Quick check (minutes)
    ├── medium.cfg              # Thorough check (hours)
    └── exhaustive.cfg          # Full verification (days)
```

### 3.2 Core Specification: KrepisUniverse.tla

```tla
---------------------------- MODULE KrepisUniverse ----------------------------
\* Krepis Digital Twin Simulator - Master Specification
\* 
\* This is the top-level specification that composes all modules
\* and defines the physical laws of the simulated universe.

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ============================================================================
\* CONSTANTS - Configuration Parameters
\* ============================================================================

CONSTANTS
    Tenants,                \* Set of tenant IDs
    MaxVirtualTimeNs,       \* Maximum virtual time (for bounded model checking)
    MaxHeapMB,              \* Per-tenant heap limit
    MaxExecTimeNs,          \* Per-tenant execution time limit
    MaxConcurrent,          \* Per-tenant concurrent execution limit
    NumCores                \* Number of simulated CPU cores

\* ============================================================================
\* VARIABLES - System State
\* ============================================================================

VARIABLES
    \* Virtual Clock State
    virtualTimeNs,          \* Current virtual time (nanoseconds)
    lamportClock,           \* Lamport logical clock
    eventQueue,             \* Priority queue of scheduled events
    
    \* Memory State
    mainMemory,             \* Main memory: address -> value
    storeBuffers,           \* Per-core store buffers
    cacheState,             \* Per-line cache state (MESI)
    
    \* Scheduler State
    tasks,                  \* Task registry: taskId -> task state
    runQueue,               \* Queue of runnable tasks
    currentTask,            \* Currently executing task (per core)
    mutexes,                \* Mutex state: mutexId -> holder
    
    \* Kernel State
    tenantState,            \* Per-tenant metadata
    isolatePool,            \* V8 isolate pool
    journal                 \* Transaction journal

\* All variables
vars == <<virtualTimeNs, lamportClock, eventQueue, mainMemory, storeBuffers,
          cacheState, tasks, runQueue, currentTask, mutexes, tenantState,
          isolatePool, journal>>

\* ============================================================================
\* TYPE INVARIANTS
\* ============================================================================

TypeInvariant ==
    /\ virtualTimeNs \in 0..MaxVirtualTimeNs
    /\ lamportClock \in Nat
    /\ eventQueue \in Seq([scheduledAt: Nat, lamport: Nat, eventId: Nat, payload: STRING])
    /\ \A t \in Tenants: tenantState[t] \in [
           heapUsage: 0..MaxHeapMB,
           execTime: 0..MaxExecTimeNs,
           concurrent: 0..MaxConcurrent,
           active: BOOLEAN
       ]

\* ============================================================================
\* SAFETY INVARIANTS (Things that must ALWAYS hold)
\* ============================================================================

\* [S-001] Time Monotonicity: Time never goes backward
TimeMonotonicity ==
    [][virtualTimeNs' >= virtualTimeNs]_vars

\* [S-002] Lamport Consistency: Lamport clock increases on events
LamportConsistency ==
    [][lamportClock' >= lamportClock]_vars

\* [S-003] Event Ordering: Events fire in deterministic order
EventOrdering ==
    \A i, j \in 1..Len(eventQueue):
        i < j => 
            \/ eventQueue[i].scheduledAt < eventQueue[j].scheduledAt
            \/ (eventQueue[i].scheduledAt = eventQueue[j].scheduledAt
                /\ eventQueue[i].lamport <= eventQueue[j].lamport)

\* [S-004] Heap Limit: No tenant exceeds heap limit
HeapLimitRespected ==
    \A t \in Tenants: tenantState[t].heapUsage <= MaxHeapMB

\* [S-005] Execution Limit: Watchdog terminates over-limit execution
WatchdogEnforced ==
    \A t \in Tenants:
        tenantState[t].execTime > MaxExecTimeNs =>
            ~tenantState[t].active

\* [S-006] Concurrency Limit: Bulkhead pattern enforced
ConcurrencyLimitRespected ==
    \A t \in Tenants: tenantState[t].concurrent <= MaxConcurrent

\* [S-007] Tenant Isolation: No cross-tenant memory access
TenantIsolation ==
    \A t1, t2 \in Tenants:
        t1 # t2 =>
            Disjoint(MemoryRegion(t1), MemoryRegion(t2))

\* [S-008] Deadlock Freedom: No circular wait
NoDeadlock ==
    ~(\E cycle \in Cycles(WaitForGraph): cycle # <<>>)

\* Combined Safety Property
Safety ==
    /\ TypeInvariant
    /\ TimeMonotonicity
    /\ LamportConsistency
    /\ EventOrdering
    /\ HeapLimitRespected
    /\ WatchdogEnforced
    /\ ConcurrencyLimitRespected
    /\ TenantIsolation
    /\ NoDeadlock

\* ============================================================================
\* LIVENESS PROPERTIES (Things that must EVENTUALLY happen)
\* ============================================================================

\* [L-001] Progress: Scheduled events eventually fire
EventualExecution ==
    \A e \in Range(eventQueue):
        <>(~(e \in Range(eventQueue')))

\* [L-002] Fairness: No task starves
NoStarvation ==
    \A t \in DOMAIN tasks:
        tasks[t].state = "Runnable" ~> tasks[t].state = "Running"

\* [L-003] Termination: Bounded executions terminate
BoundedTermination ==
    \A t \in Tenants:
        tenantState[t].active ~>
            (\/ ~tenantState[t].active
             \/ tenantState[t].execTime > MaxExecTimeNs)

\* Combined Liveness Property
Liveness ==
    /\ EventualExecution
    /\ NoStarvation
    /\ BoundedTermination

\* ============================================================================
\* STATE TRANSITIONS (Actions)
\* ============================================================================

\* Time tick action
Tick ==
    /\ eventQueue # <<>>
    /\ LET nextEvent == Head(eventQueue)
       IN /\ virtualTimeNs' = nextEvent.scheduledAt
          /\ lamportClock' = lamportClock + 1
          /\ eventQueue' = Tail(eventQueue)
          /\ ProcessEvent(nextEvent)
    /\ UNCHANGED <<mainMemory, storeBuffers, cacheState, mutexes>>

\* Schedule new event
ScheduleEvent(delay, payload) ==
    /\ LET newEvent == [
           scheduledAt |-> virtualTimeNs + delay,
           lamport |-> lamportClock,
           eventId |-> NextEventId(),
           payload |-> payload
       ]
       IN eventQueue' = SortedInsert(eventQueue, newEvent)
    /\ lamportClock' = lamportClock + 1
    /\ UNCHANGED <<virtualTimeNs, mainMemory, storeBuffers, cacheState,
                   tasks, runQueue, currentTask, mutexes, tenantState,
                   isolatePool, journal>>

\* Memory write action
MemoryWrite(core, addr, value, ordering) ==
    /\ CASE ordering = "SeqCst" ->
            /\ FlushAllStoreBuffers
            /\ mainMemory' = [mainMemory EXCEPT ![addr] = value]
            /\ InvalidateCacheLine(CacheLineOf(addr))
         [] ordering = "Release" ->
            /\ FlushStoreBuffer(core)
            /\ mainMemory' = [mainMemory EXCEPT ![addr] = value]
         [] ordering \in {"Relaxed", "Acquire"} ->
            /\ storeBuffers' = [storeBuffers EXCEPT ![core] = 
                   Append(@, [addr |-> addr, value |-> value])]
            /\ UNCHANGED mainMemory
    /\ UNCHANGED <<virtualTimeNs, lamportClock, eventQueue, cacheState,
                   tasks, runQueue, currentTask, mutexes, tenantState,
                   isolatePool, journal>>

\* Task spawn action
SpawnTask(tenant, priority) ==
    /\ tenantState[tenant].concurrent < MaxConcurrent
    /\ LET newTaskId == NextTaskId()
           newTask == [
               id |-> newTaskId,
               tenant |-> tenant,
               state |-> "Runnable",
               priority |-> priority
           ]
       IN /\ tasks' = tasks @@ (newTaskId :> newTask)
          /\ runQueue' = Append(runQueue, newTaskId)
          /\ tenantState' = [tenantState EXCEPT
                 ![tenant].concurrent = @ + 1]
    /\ UNCHANGED <<virtualTimeNs, lamportClock, eventQueue, mainMemory,
                   storeBuffers, cacheState, currentTask, mutexes,
                   isolatePool, journal>>

\* Watchdog termination action
WatchdogTerminate(tenant) ==
    /\ tenantState[tenant].execTime > MaxExecTimeNs
    /\ tenantState' = [tenantState EXCEPT ![tenant].active = FALSE]
    /\ journal' = Append(journal, [
           type |-> "WatchdogTermination",
           tenant |-> tenant,
           time |-> virtualTimeNs
       ])
    /\ UNCHANGED <<virtualTimeNs, lamportClock, eventQueue, mainMemory,
                   storeBuffers, cacheState, tasks, runQueue, currentTask,
                   mutexes, isolatePool>>

\* ============================================================================
\* SPECIFICATION
\* ============================================================================

Init ==
    /\ virtualTimeNs = 0
    /\ lamportClock = 0
    /\ eventQueue = <<>>
    /\ mainMemory = [a \in Addresses |-> 0]
    /\ storeBuffers = [c \in 1..NumCores |-> <<>>]
    /\ cacheState = [l \in CacheLines |-> "Invalid"]
    /\ tasks = <<>>
    /\ runQueue = <<>>
    /\ currentTask = [c \in 1..NumCores |-> NULL]
    /\ mutexes = [m \in MutexIds |-> NULL]
    /\ tenantState = [t \in Tenants |-> [
           heapUsage |-> 0,
           execTime |-> 0,
           concurrent |-> 0,
           active |-> TRUE
       ]]
    /\ isolatePool = <<>>
    /\ journal = <<>>

Next ==
    \/ Tick
    \/ \E delay \in 1..1000, payload \in Payloads: ScheduleEvent(delay, payload)
    \/ \E core \in 1..NumCores, addr \in Addresses, value \in Values, 
          ordering \in {"SeqCst", "Acquire", "Release", "Relaxed"}:
          MemoryWrite(core, addr, value, ordering)
    \/ \E tenant \in Tenants, priority \in 1..255: SpawnTask(tenant, priority)
    \/ \E tenant \in Tenants: WatchdogTerminate(tenant)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ============================================================================
\* THEOREMS TO VERIFY
\* ============================================================================

THEOREM Spec => []Safety
THEOREM Spec => Liveness

=============================================================================
```

---

## 4. Invariant Catalog

### 4.1 Safety Invariants

| ID | Name | Module | Description | TLA+ Expression |
|----|------|--------|-------------|-----------------|
| S-001 | TimeMonotonicity | VirtualClock | Time never decreases | `[][virtualTimeNs' >= virtualTimeNs]_vars` |
| S-002 | LamportConsistency | VirtualClock | Lamport increases | `[][lamportClock' >= lamportClock]_vars` |
| S-003 | EventOrdering | VirtualClock | Events ordered | See spec |
| S-004 | HeapLimitRespected | SovereignKernel | Heap within limit | `\A t: heapUsage <= MaxHeapMB` |
| S-005 | WatchdogEnforced | SovereignKernel | Timeout terminates | `execTime > Max => ~active` |
| S-006 | ConcurrencyLimit | SovereignKernel | Bulkhead enforced | `\A t: concurrent <= MaxConcurrent` |
| S-007 | TenantIsolation | SovereignKernel | No cross-tenant | `Disjoint(regions)` |
| S-008 | NoDeadlock | SchedulerOracle | No circular wait | `~Cycles(WaitForGraph)` |

### 4.2 Liveness Invariants

| ID | Name | Module | Description | TLA+ Expression |
|----|------|--------|-------------|-----------------|
| L-001 | EventualExecution | VirtualClock | Events fire | `\A e: <>(e \notin queue)` |
| L-002 | NoStarvation | SchedulerOracle | Tasks run | `Runnable ~> Running` |
| L-003 | BoundedTermination | SovereignKernel | Executions end | `active ~> ~active` |

---

## 5. Model Checking Configuration

### 5.1 Configuration Files

#### Small Configuration (CI Quick Check)
```
\* configs/small.cfg

CONSTANTS
    Tenants = {"t1", "t2"}
    MaxVirtualTimeNs = 1000
    MaxHeapMB = 128
    MaxExecTimeNs = 100
    MaxConcurrent = 2
    NumCores = 2

SPECIFICATION Spec
INVARIANTS Safety
PROPERTIES Liveness

\* Estimated time: 2-5 minutes
```

#### Medium Configuration (Nightly Build)
```
\* configs/medium.cfg

CONSTANTS
    Tenants = {"t1", "t2", "t3", "t4"}
    MaxVirtualTimeNs = 10000
    MaxHeapMB = 256
    MaxExecTimeNs = 500
    MaxConcurrent = 5
    NumCores = 4

SPECIFICATION Spec
INVARIANTS Safety
PROPERTIES Liveness

\* Estimated time: 1-4 hours
```

#### Exhaustive Configuration (Release Verification)
```
\* configs/exhaustive.cfg

CONSTANTS
    Tenants = {"t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8"}
    MaxVirtualTimeNs = 100000
    MaxHeapMB = 512
    MaxExecTimeNs = 1000
    MaxConcurrent = 10
    NumCores = 8

SPECIFICATION Spec
INVARIANTS Safety
PROPERTIES Liveness

CHECK_DEADLOCK TRUE
SYMMETRY TenantSymmetry

\* Estimated time: 1-7 days
```

### 5.2 State Space Reduction

```tla
\* Symmetry reduction for tenants (all tenants are equivalent)
TenantSymmetry == Permutations(Tenants)

\* View abstraction (reduce state space by ignoring irrelevant details)
View == <<
    virtualTimeNs,
    Cardinality({t \in Tenants: tenantState[t].active}),
    Len(eventQueue)
>>
```

#### Memory Fence State Coalescing

The Relaxed memory model causes exponential state explosion due to store buffer permutations. We optimize by **merging states only at memory fence points**:

```tla
\* Coalesced Memory View (reduces state space by 10-100x for relaxed models)
\* 
\* Instead of tracking every store buffer state:
\*   state = (mainMemory, storeBuffer[core1], storeBuffer[core2], ...)
\* 
\* We track only "observable states" after fences:
\*   state = (observableMemory, pendingWriteCount)

CoalescedMemoryView == <<
    \* Merge store buffers into main memory on fence
    IF \E core \in 1..NumCores: lastOp[core] = "Fence"
    THEN mainMemory @@ MergedStoreBuffers
    ELSE mainMemory,
    
    \* Track pending writes count (not contents)
    SUM([core \in 1..NumCores |-> Len(storeBuffers[core])])
>>

\* State merge trigger: Only record distinct states after synchronization
StateMergeTrigger ==
    \/ \E core: lastOp[core] \in {"SeqCst", "Fence", "Release"}
    \/ \E core: lastOp[core] = "Acquire" /\ paired_with_release
```

#### Temporal Logic Constraints (Partial Order Focus)

Rather than tracking absolute time values (which explode state space), we focus on **relative ordering between events**:

```tla
\* OPTIMIZATION: Partial Order Reduction for Time
\* 
\* Instead of: virtualTimeNs \in 0..MaxTime (millions of states)
\* We use: HappensBefore relation (polynomial states)

HappensBefore == 
    { <<e1, e2>> \in Events \X Events :
        \/ e1.lamport < e2.lamport
        \/ (e1.lamport = e2.lamport /\ e1.eventId < e2.eventId)
    }

\* Time is abstracted to "epochs" between events
TimeEpoch == Cardinality({ e \in FiredEvents : TRUE })

\* Invariants rewritten in terms of ordering, not absolute time
TimeMonotonicity_PO ==
    \A e1, e2 \in Events:
        <<e1, e2>> \in HappensBefore => e1.epoch <= e2.epoch

\* This reduces state space from O(MaxTime) to O(|Events|^2)
```

#### Reduction Impact Summary

| Technique | State Reduction | When to Apply |
|-----------|-----------------|---------------|
| Tenant Symmetry | N! → 1 | Always for identical tenants |
| View Abstraction | 10-100x | Memory-intensive models |
| Memory Fence Coalescing | 10-100x | Relaxed memory model |
| Partial Order Focus | MaxTime → \|Events\|² | Time-sensitive specs |
| DPOR (Dynamic) | Exponential | Concurrent operations |

---

## 6. Trace Validation Pipeline

### 6.1 Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    TRACE VALIDATION PIPELINE                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌──────────────┐                                                       │
│  │  Simulator   │                                                       │
│  │  Execution   │                                                       │
│  └──────┬───────┘                                                       │
│         │                                                               │
│         ▼                                                               │
│  ┌──────────────┐     ┌──────────────┐     ┌──────────────┐           │
│  │    Trace     │────▶│    TLA+      │────▶│     TLC      │           │
│  │   Recorder   │     │   Exporter   │     │   Validator  │           │
│  └──────────────┘     └──────────────┘     └──────┬───────┘           │
│                                                    │                    │
│                              ┌────────────────────┬┘                   │
│                              ▼                    ▼                     │
│                       ┌──────────────┐     ┌──────────────┐           │
│                       │   PASS       │     │    FAIL      │           │
│                       │   Report     │     │   + Counter  │           │
│                       │              │     │   Example    │           │
│                       └──────────────┘     └──────────────┘           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 6.2 Trace to TLA+ Conversion

```rust
// crates/krepis-twin/src/verification/tla_exporter.rs

pub struct TlaExporter {
    module_name: String,
}

impl TlaExporter {
    /// Convert execution trace to TLA+ state sequence
    pub fn export(&self, trace: &ExecutionTrace) -> String {
        let mut output = String::new();
        
        // Module header
        output.push_str(&format!("---- MODULE {} ----\n", self.module_name));
        output.push_str("EXTENDS KrepisUniverse, TLC\n\n");
        
        // State sequence
        output.push_str("TraceStates == <<\n");
        
        for (i, state) in trace.states.iter().enumerate() {
            output.push_str(&self.state_to_tla(state));
            if i < trace.states.len() - 1 {
                output.push_str(",\n");
            }
        }
        
        output.push_str("\n>>\n\n");
        
        // Validation formula
        output.push_str("TraceValid ==\n");
        output.push_str("    /\\ Len(TraceStates) > 0\n");
        output.push_str("    /\\ \\A i \\in 1..Len(TraceStates): ");
        output.push_str("TypeInvariant' = TRUE\n");
        output.push_str("    /\\ \\A i \\in 1..(Len(TraceStates)-1):\n");
        output.push_str("         LET s1 == TraceStates[i]\n");
        output.push_str("             s2 == TraceStates[i+1]\n");
        output.push_str("         IN s2.virtualTimeNs >= s1.virtualTimeNs\n");
        
        output.push_str("\n====\n");
        
        output
    }
    
    fn state_to_tla(&self, state: &SimulatorState) -> String {
        format!(
            "  [virtualTimeNs |-> {}, lamportClock |-> {}, \
             tenantState |-> {}]",
            state.virtual_time_ns,
            state.lamport_clock,
            self.tenant_states_to_tla(&state.tenant_states)
        )
    }
    
    fn tenant_states_to_tla(&self, states: &HashMap<String, TenantState>) -> String {
        let entries: Vec<String> = states.iter()
            .map(|(id, state)| {
                format!(
                    "\"{}\" :> [heapUsage |-> {}, execTime |-> {}, \
                     concurrent |-> {}, active |-> {}]",
                    id,
                    state.heap_usage_mb,
                    state.exec_time_ns,
                    state.concurrent,
                    if state.active { "TRUE" } else { "FALSE" }
                )
            })
            .collect();
        
        format!("[{}]", entries.join(", "))
    }
}
```

### 6.3 Validation Execution

```rust
pub struct TlaValidator {
    tlc_path: PathBuf,
    spec_path: PathBuf,
}

impl TlaValidator {
    /// Validate trace against TLA+ specification
    pub fn validate(&self, trace: &ExecutionTrace) -> Result<ValidationResult, ValidationError> {
        // Export trace
        let exporter = TlaExporter::new("TraceValidation");
        let tla_module = exporter.export(trace);
        
        // Write to temp file
        let trace_path = std::env::temp_dir().join("trace_validation.tla");
        std::fs::write(&trace_path, &tla_module)?;
        
        // Run TLC
        let output = Command::new("java")
            .args(&[
                "-jar", self.tlc_path.to_str().unwrap(),
                "-config", self.spec_path.to_str().unwrap(),
                "-workers", "auto",
                trace_path.to_str().unwrap(),
            ])
            .output()?;
        
        // Parse output
        self.parse_output(&output.stdout, &output.stderr)
    }
    
    fn parse_output(&self, stdout: &[u8], stderr: &[u8]) -> Result<ValidationResult, ValidationError> {
        let stdout_str = String::from_utf8_lossy(stdout);
        
        if stdout_str.contains("No error has been found") {
            Ok(ValidationResult::Valid)
        } else if stdout_str.contains("Invariant") && stdout_str.contains("violated") {
            // Extract violated invariant and counter-example
            let invariant = self.extract_invariant(&stdout_str);
            let counter_example = self.extract_counter_example(&stdout_str);
            
            Ok(ValidationResult::Violated {
                invariant,
                counter_example,
            })
        } else {
            Err(ValidationError::TlcError(stdout_str.to_string()))
        }
    }
}
```

---

## 7. Violation Recovery Procedure

### 7.1 Automatic Response

When a trace violates a TLA+ invariant:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    VIOLATION RESPONSE WORKFLOW                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  1. IMMEDIATE (< 1 second)                                             │
│     ├── CI pipeline marks build as FAILED                              │
│     ├── Counter-example saved to artifacts/violations/                 │
│     └── Alert sent to #krepis-critical Slack channel                   │
│                                                                         │
│  2. AUTOMATED ANALYSIS (< 5 minutes)                                   │
│     ├── Trace reducer minimizes counter-example                        │
│     ├── Root cause analyzer identifies likely cause                    │
│     └── Related test cases flagged for review                          │
│                                                                         │
│  3. HUMAN REVIEW (< 24 hours)                                          │
│     ├── Architect reviews counter-example                              │
│     ├── Decision: spec bug vs implementation bug                       │
│     └── Fix assigned and prioritized                                   │
│                                                                         │
│  4. VERIFICATION (before merge)                                        │
│     ├── Fix verified with original counter-example                     │
│     ├── Regression test added                                          │
│     └── TLC re-run confirms no new violations                          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 7.2 Counter-Example Analysis

```rust
pub struct CounterExampleAnalyzer {
    spec: TlaSpec,
}

impl CounterExampleAnalyzer {
    /// Analyze counter-example to find root cause
    pub fn analyze(&self, counter_example: &CounterExample) -> AnalysisReport {
        let mut report = AnalysisReport::new();
        
        // 1. Identify violated invariant
        report.violated_invariant = counter_example.invariant.clone();
        
        // 2. Find the transition that caused violation
        let violation_transition = self.find_violation_transition(counter_example);
        report.violation_transition = violation_transition;
        
        // 3. Trace back causal chain
        let causal_chain = self.trace_causality(counter_example, &violation_transition);
        report.causal_chain = causal_chain;
        
        // 4. Suggest likely root causes
        report.likely_causes = self.suggest_causes(&report);
        
        // 5. Generate minimal reproduction
        report.minimal_reproduction = self.minimize(counter_example);
        
        report
    }
    
    fn suggest_causes(&self, report: &AnalysisReport) -> Vec<LikelyCause> {
        let mut causes = Vec::new();
        
        match &report.violated_invariant {
            Invariant::TimeMonotonicity => {
                causes.push(LikelyCause {
                    probability: 0.8,
                    description: "Race condition in VirtualClock::tick()".to_string(),
                    suggested_fix: "Ensure fetch_max is used for time updates".to_string(),
                });
            }
            Invariant::HeapLimitRespected => {
                causes.push(LikelyCause {
                    probability: 0.7,
                    description: "GC not triggered before allocation check".to_string(),
                    suggested_fix: "Add GC call before heap limit check".to_string(),
                });
            }
            Invariant::NoDeadlock => {
                causes.push(LikelyCause {
                    probability: 0.9,
                    description: "Lock ordering violation".to_string(),
                    suggested_fix: "Enforce global lock ordering".to_string(),
                });
            }
            // ... other invariants
            _ => {}
        }
        
        causes
    }
}
```

### 7.3 Automatic Edge Case Matrix Matching

When a violation occurs, the analyzer automatically cross-references with the Edge Case Matrix to identify known failure patterns:

```rust
pub struct EdgeCaseMatcher {
    matrix: EdgeCaseMatrix,
}

impl EdgeCaseMatcher {
    /// Match counter-example against Edge Case Matrix
    /// 
    /// # Returns
    /// Matched edge cases with confidence scores
    pub fn match_counter_example(&self, ce: &CounterExample) -> Vec<EdgeCaseMatch> {
        let mut matches = Vec::new();
        
        // Extract signature from counter-example
        let signature = self.extract_signature(ce);
        
        // Pattern matching against known edge cases
        for edge_case in &self.matrix.cases {
            let similarity = self.compute_similarity(&signature, &edge_case.pattern);
            
            if similarity > 0.7 {
                matches.push(EdgeCaseMatch {
                    edge_case_id: edge_case.id.clone(),
                    confidence: similarity,
                    matched_features: self.extract_matched_features(&signature, &edge_case.pattern),
                    suggested_test: edge_case.test_strategy.clone(),
                    doc_link: format!("docs/EDGE_CASE_MATRIX.md#{}", edge_case.id),
                });
            }
        }
        
        // Sort by confidence
        matches.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
        matches
    }
    
    fn extract_signature(&self, ce: &CounterExample) -> ViolationSignature {
        ViolationSignature {
            invariant: ce.invariant.clone(),
            state_diff: self.compute_state_diff(ce),
            action_sequence: self.extract_action_sequence(ce),
            involved_resources: self.extract_resources(ce),
        }
    }
    
    fn compute_similarity(&self, sig: &ViolationSignature, pattern: &EdgeCasePattern) -> f64 {
        let mut score = 0.0;
        let mut weight_sum = 0.0;
        
        // Invariant match (weight: 0.4)
        if sig.invariant == pattern.expected_invariant {
            score += 0.4;
        }
        weight_sum += 0.4;
        
        // Action sequence similarity (weight: 0.3)
        let action_sim = self.jaccard_similarity(&sig.action_sequence, &pattern.action_pattern);
        score += 0.3 * action_sim;
        weight_sum += 0.3;
        
        // Resource involvement (weight: 0.3)
        let resource_sim = self.resource_overlap(&sig.involved_resources, &pattern.resources);
        score += 0.3 * resource_sim;
        weight_sum += 0.3;
        
        score / weight_sum
    }
}

/// Integration with analysis report
impl CounterExampleAnalyzer {
    pub fn analyze_with_edge_cases(&self, ce: &CounterExample) -> EnhancedAnalysisReport {
        let base_report = self.analyze(ce);
        let matcher = EdgeCaseMatcher::new(&self.edge_case_matrix);
        let edge_case_matches = matcher.match_counter_example(ce);
        
        EnhancedAnalysisReport {
            base: base_report,
            edge_case_matches,
            recommended_actions: self.generate_recommendations(&edge_case_matches),
        }
    }
    
    fn generate_recommendations(&self, matches: &[EdgeCaseMatch]) -> Vec<Recommendation> {
        matches.iter().map(|m| {
            Recommendation {
                priority: if m.confidence > 0.9 { "High" } else { "Medium" }.to_string(),
                action: format!(
                    "Review edge case {} in EDGE_CASE_MATRIX.md", 
                    m.edge_case_id
                ),
                test_to_add: m.suggested_test.clone(),
                documentation: m.doc_link.clone(),
            }
        }).collect()
    }
}
```

#### Example Output

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    VIOLATION ANALYSIS REPORT                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  Violated Invariant: NoDeadlock                                        │
│  Transition: MutexLock(task_2, mutex_a)                                │
│                                                                         │
│  ═══ EDGE CASE MATRIX MATCHES ═══                                      │
│                                                                         │
│  1. S-EC-010 (Simple Deadlock) - 94% confidence                        │
│     ├── Pattern: Circular wait A→B, B→A                                │
│     ├── Matched: 2 tasks, 2 mutexes, circular dependency              │
│     └── Test: test_simple_deadlock_detection()                         │
│                                                                         │
│  2. S-EC-014 (Lock Order Violation) - 78% confidence                   │
│     ├── Pattern: Inconsistent lock ordering                            │
│     ├── Matched: Different lock order across tasks                    │
│     └── Test: test_lock_order_violation()                              │
│                                                                         │
│  ═══ RECOMMENDED ACTIONS ═══                                           │
│                                                                         │
│  [HIGH] Review S-EC-010 in docs/EDGE_CASE_MATRIX.md#S-EC-010           │
│  [MED]  Add regression test for this specific lock sequence            │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 8. CI/CD Integration

### 8.1 GitHub Actions Workflow

```yaml
# .github/workflows/formal-verification.yml

name: Formal Verification

on:
  push:
    branches: [main, develop]
    paths:
      - 'crates/krepis-twin/**'
      - 'specs/tla/**'
  pull_request:
    paths:
      - 'crates/krepis-twin/**'
      - 'specs/tla/**'
  schedule:
    # Nightly exhaustive verification
    - cron: '0 2 * * *'

env:
  TLA_TOOLS_VERSION: '1.8.0'

jobs:
  tla-syntax:
    name: TLA+ Syntax Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install TLA+ Tools
        run: |
          wget -q "https://github.com/tlaplus/tlaplus/releases/download/v${TLA_TOOLS_VERSION}/tla2tools.jar"
          
      - name: Syntax Check
        run: |
          for spec in specs/tla/**/*.tla; do
            java -jar tla2tools.jar -SANY "$spec"
          done

  tla-quick:
    name: TLA+ Quick Check
    needs: tla-syntax
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install TLA+ Tools
        run: wget -q "https://github.com/tlaplus/tlaplus/releases/download/v${TLA_TOOLS_VERSION}/tla2tools.jar"
        
      - name: Run TLC (Small Config)
        run: |
          java -jar tla2tools.jar \
            -config specs/tla/configs/small.cfg \
            -workers auto \
            -deadlock \
            specs/tla/KrepisUniverse.tla
        timeout-minutes: 10
        
  tla-thorough:
    name: TLA+ Thorough Check
    needs: tla-quick
    if: github.event_name == 'push' && github.ref == 'refs/heads/main'
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install TLA+ Tools
        run: wget -q "https://github.com/tlaplus/tlaplus/releases/download/v${TLA_TOOLS_VERSION}/tla2tools.jar"
        
      - name: Run TLC (Medium Config)
        run: |
          java -Xmx8g -jar tla2tools.jar \
            -config specs/tla/configs/medium.cfg \
            -workers auto \
            -deadlock \
            specs/tla/KrepisUniverse.tla
        timeout-minutes: 240
        
      - name: Upload Results
        if: always()
        uses: actions/upload-artifact@v4
        with:
          name: tlc-results
          path: |
            *.out
            states/

  tla-exhaustive:
    name: TLA+ Exhaustive Check
    if: github.event_name == 'schedule'
    runs-on: [self-hosted, high-memory]
    steps:
      - uses: actions/checkout@v4
      
      - name: Run TLC (Exhaustive)
        run: |
          java -Xmx64g -jar tla2tools.jar \
            -config specs/tla/configs/exhaustive.cfg \
            -workers 16 \
            -deadlock \
            specs/tla/KrepisUniverse.tla
        timeout-minutes: 10080  # 7 days
        
      - name: Notify on Violation
        if: failure()
        uses: slackapi/slack-github-action@v1
        with:
          channel-id: 'krepis-critical'
          payload: |
            {
              "text": "🚨 TLA+ Exhaustive Check Failed!",
              "blocks": [
                {
                  "type": "section",
                  "text": {
                    "type": "mrkdwn",
                    "text": "TLA+ invariant violation detected in exhaustive check.\n*Run:* ${{ github.run_id }}"
                  }
                }
              ]
            }

  trace-validation:
    name: Trace Validation
    needs: tla-quick
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Build Simulator
        run: cargo build --release --package krepis-twin
        
      - name: Run Simulation
        run: |
          cargo run --release --package krepis-twin-runner -- \
            --iterations 100000 \
            --output traces/sim.trace
            
      - name: Validate Traces
        run: |
          cargo run --release --package krepis-twin-validator -- \
            --trace traces/sim.trace \
            --spec specs/tla/KrepisUniverse.tla
```

---

## 9. Best Practices

### 9.1 Writing TLA+ Specifications

| Practice | Description | Example |
|----------|-------------|---------|
| **Start Abstract** | Begin with high-level properties | `Time never decreases` |
| **Refine Iteratively** | Add detail in refinement layers | Abstract → Concrete |
| **Use Constants** | Parameterize bounds for flexibility | `CONSTANTS MaxTime` |
| **Symmetry Reduction** | Exploit symmetry for state reduction | `Permutations(Tenants)` |
| **Separate Concerns** | One module per concept | `VirtualClock.tla` |

### 9.2 Debugging TLA+ Failures

```
1. Read the counter-example carefully
   └── What sequence of states led to violation?

2. Identify the violated invariant
   └── Which property failed?

3. Find the critical transition
   └── Which action caused the bad state?

4. Simplify
   └── Can you reproduce with fewer tenants/events?

5. Compare with implementation
   └── Does Rust code match TLA+ action?
```

---

*"TLA+ is not optional. It is the mathematical foundation of our correctness."*

— K-ACA v2.0