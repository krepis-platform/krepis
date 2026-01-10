# 📐 Physical Laws Specification

**The Immutable Laws of the Krepis Universe**

```
Document: PHYSICAL_LAWS_SPEC
Version: 1.0.0
Status: Constitutional
Classification: Core Invariants
Cross-References:
  - Edge Cases: ../EDGE_CASE_MATRIX.md (T-EC-*, M-EC-*, S-EC-*, K-EC-*)
  - TLA+ Specs: ../TLA_VERIFICATION_STRATEGY.md#4-invariant-catalog
  - V-Levels: ../README.md#6.3-verification-levels
```

---

## 1. Overview

This document defines the **physical laws** that govern the Krepis Digital Twin Simulator. These laws are immutable constraints that must hold true at every instant of simulated time. Violation of any law indicates a fundamental bug in either the simulator or the kernel.

**Navigation**:
- For test scenarios covering these laws → [EDGE_CASE_MATRIX.md](EDGE_CASE_MATRIX.md)
- For TLA+ formal specifications → [TLA_VERIFICATION_STRATEGY.md](TLA_VERIFICATION_STRATEGY.md)
- For implementation workflow → [DEVELOPMENT_WORKFLOW.md](DEVELOPMENT_WORKFLOW.md)

---

## 2. Temporal Laws (The Flow of Time)

### Law T-001: Temporal Monotonicity

> **"Time flows forward, never backward."**

```
∀ t₁, t₂ ∈ Time: t₁ occurs before t₂ ⟹ value(t₁) ≤ value(t₂)
```

#### Formal Definition

```rust
/// The clock must satisfy this property at all times
pub trait TemporalMonotonicity {
    /// After any operation, now() must be >= previous now()
    fn invariant(&self) -> bool {
        let t1 = self.now_ns();
        // ... any operations ...
        let t2 = self.now_ns();
        t2 >= t1
    }
}
```

#### Implementation Constraints

| Constraint | Requirement | Rationale |
|------------|-------------|-----------|
| Counter type | `AtomicU64` | No overflow for 584 years |
| Update operation | `fetch_max` | Ensures monotonicity |
| Memory ordering | `Ordering::Release` | Visibility guarantee |

#### Violation Scenarios

| Scenario | Cause | Prevention |
|----------|-------|------------|
| Counter wrap | 64-bit overflow | Panic on overflow attempt |
| Concurrent decrement | Race condition | `fetch_max` only |
| Corrupted state | Memory corruption | Checksums, Kani proofs |

---

### Law T-002: Event Causality Preservation

> **"Effects cannot precede their causes."**

```
∀ e₁, e₂ ∈ Events: e₁ causes e₂ ⟹ timestamp(e₁) < timestamp(e₂)
```

#### Formal Definition

```rust
/// Causal relationship between events
pub struct CausalEdge {
    pub cause: EventId,
    pub effect: EventId,
}

impl CausalEdge {
    /// This invariant must hold for all causal edges
    pub fn invariant(&self, trace: &ExecutionTrace) -> bool {
        let cause_event = trace.get(self.cause);
        let effect_event = trace.get(self.effect);
        
        // Timestamp ordering
        cause_event.virtual_time_ns <= effect_event.virtual_time_ns
        // Lamport ordering (strict)
        && cause_event.lamport < effect_event.lamport
    }
}
```

#### Causality Sources

| Source | Example | Lamport Update |
|--------|---------|----------------|
| Message send/receive | IPC, channel | receiver.lamport = max(receiver, sender) + 1 |
| Memory dependency | Write → Read | reader.lamport = max(reader, writer) + 1 |
| Synchronization | Lock acquire | acquirer.lamport = max(acquirer, releaser) + 1 |
| Task spawn | Parent → Child | child.lamport = parent.lamport + 1 |

---

### Law T-003: Event Ordering Determinism

> **"Same events, same schedule, same order. Always."**

```
∀ S₁, S₂ ∈ Schedules: 
    events(S₁) = events(S₂) ∧ seed(S₁) = seed(S₂)
    ⟹ order(S₁) = order(S₂)
```

#### Total Ordering Key

Events are ordered by a composite key that guarantees total ordering:

```rust
/// The composite ordering key
#[derive(Ord, PartialOrd, Eq, PartialEq)]
pub struct EventOrderingKey {
    /// Primary: Virtual time in nanoseconds
    pub virtual_time_ns: u64,
    
    /// Secondary: Lamport timestamp (causal ordering)
    pub lamport: u64,
    
    /// Tertiary: Unique event ID (scheduling order)
    pub event_id: u64,
}
```

#### Ordering Priority

```
┌─────────────────────────────────────────────────────────────────────┐
│                     EVENT ORDERING PRIORITY                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   Priority 1: Virtual Time (ns)                                     │
│   ├── Earlier scheduled time wins                                   │
│   └── Guarantees temporal ordering                                  │
│                                                                     │
│   Priority 2: Lamport Timestamp (ties in time)                      │
│   ├── Lower Lamport wins (older causality)                          │
│   └── Preserves causal ordering when times equal                    │
│                                                                     │
│   Priority 3: Event ID (ties in time AND lamport)                   │
│   ├── Lower ID wins (earlier scheduled)                             │
│   └── Provides deterministic tie-breaking                           │
│                                                                     │
│   Result: TOTAL ORDER - No ambiguity ever                           │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

### Law T-004: Discrete Time Progression

> **"Time advances in quanta, not continuously."**

```
∀ tick ∈ Ticks: Δtime(tick) ∈ {event_jump, fixed_interval}
```

#### Time Progression Modes

| Mode | Progression | Use Case | Determinism |
|------|-------------|----------|-------------|
| `EventDriven` | Jump to next event | High-speed simulation | ✅ Full |
| `FixedTick` | Fixed ns increment | Timing analysis | ✅ Full |
| `RealTime` | Sync with wall-clock | Integration test | ⚠️ Partial |

#### Event-Driven Time Jump

```rust
impl VirtualClock {
    fn compute_next_time_event_driven(&self) -> u64 {
        self.event_heap
            .lock()
            .peek()
            .map(|e| e.scheduled_at_ns)
            .unwrap_or(self.current_ns.load(Ordering::Acquire))
    }
}
```

---

## 3. Spatial Laws (The Fabric of Memory)

### Law M-001: Memory Sequential Consistency

> **"Under SeqCst, all observers see the same history."**

```
∀ op₁, op₂ ∈ SeqCst_Operations:
    global_order(op₁, op₂) is consistent across all threads
```

#### Memory Ordering Hierarchy

```
┌─────────────────────────────────────────────────────────────────────┐
│                   MEMORY ORDERING HIERARCHY                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│   SeqCst (Strongest)                                                │
│   ├── Total order visible to all threads                            │
│   ├── Flushes all store buffers                                     │
│   └── Most expensive, but safest                                    │
│                                                                     │
│   Acquire                                                           │
│   ├── Prevents reads from being reordered before                    │
│   ├── Use after: lock acquire, atomic load                          │
│   └── Establishes "synchronizes-with" edge                          │
│                                                                     │
│   Release                                                           │
│   ├── Prevents writes from being reordered after                    │
│   ├── Use before: lock release, atomic store                        │
│   └── Pairs with Acquire for data transfer                          │
│                                                                     │
│   Relaxed (Weakest)                                                 │
│   ├── No ordering guarantees                                        │
│   ├── Only atomicity guaranteed                                     │
│   └── Use for: counters, statistics                                 │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

#### Implementation

```rust
impl SimulatedMemory {
    pub fn read_seqcst(&self, addr: usize, size: usize) -> Vec<u8> {
        // 1. Flush ALL store buffers (global synchronization)
        self.flush_all_store_buffers();
        
        // 2. Read from main memory (now consistent)
        self.read_main_memory(addr, size)
    }
    
    pub fn write_seqcst(&self, addr: usize, value: &[u8]) {
        // 1. Flush ALL store buffers
        self.flush_all_store_buffers();
        
        // 2. Write directly to main memory
        self.write_main_memory(addr, value);
        
        // 3. Invalidate other caches (MESI protocol)
        self.invalidate_cache_line(Self::cache_line_of(addr));
    }
}
```

---

### Law M-002: Atomic Operation Integrity

> **"Atomic operations are indivisible."**

```
∀ atomic_op ∈ AtomicOperations:
    ¬∃ intermediate_state observable during atomic_op
```

#### Guaranteed Atomic Operations

| Operation | Size Limit | Implementation |
|-----------|------------|----------------|
| Load | 8 bytes | Single memory read |
| Store | 8 bytes | Single memory write |
| CAS | 8 bytes | Lock-protected read-modify-write |
| Fetch-Add | 8 bytes | Lock-protected arithmetic |
| Exchange | 8 bytes | Lock-protected swap |

#### CAS Implementation

```rust
impl SimulatedMemory {
    /// Compare-and-swap with atomicity guarantee
    pub fn compare_and_swap(
        &self,
        addr: usize,
        expected: &[u8],
        desired: &[u8],
        _ordering: MemoryOrdering,
    ) -> (bool, Vec<u8>) {
        // CAS is always effectively SeqCst
        // Lock the entire cache line to prevent torn operations
        let line = Self::cache_line_of(addr);
        let _lock = self.line_locks.get(&line).unwrap().lock();
        
        // Atomic read-compare-write
        let current = self.read_main_memory(addr, expected.len());
        
        if current == expected {
            self.write_main_memory(addr, desired);
            (true, current)
        } else {
            (false, current)
        }
    }
}
```

---

### Law M-003: Cache Line Granularity

> **"Memory is organized in 64-byte lines."**

```
∀ addr ∈ Addresses:
    cache_line(addr) = addr & ~(64 - 1)
    false_sharing(addr₁, addr₂) ⟺ cache_line(addr₁) = cache_line(addr₂) ∧ addr₁ ≠ addr₂
```

#### Cache Line Alignment

```rust
/// Cache line constants
pub const CACHE_LINE_SIZE: usize = 64;
pub const CACHE_LINE_MASK: usize = !(CACHE_LINE_SIZE - 1);

/// Get cache line for an address
#[inline(always)]
pub fn cache_line_of(addr: usize) -> usize {
    addr & CACHE_LINE_MASK
}

/// Check for false sharing
#[inline(always)]
pub fn false_sharing(addr1: usize, addr2: usize) -> bool {
    cache_line_of(addr1) == cache_line_of(addr2) && addr1 != addr2
}
```

#### False Sharing Detection

```rust
impl SimulatedMemory {
    /// Detect false sharing during simulation
    pub fn detect_false_sharing(&self) -> Vec<FalseSharingIncident> {
        let log = self.access_log.lock();
        let mut incidents = Vec::new();
        
        // Group accesses by cache line
        let mut by_line: HashMap<usize, Vec<&MemoryAccess>> = HashMap::new();
        for access in log.iter() {
            by_line.entry(cache_line_of(access.address))
                .or_default()
                .push(access);
        }
        
        // Find lines with multiple writers to different addresses
        for (line, accesses) in by_line {
            let writers: HashSet<_> = accesses.iter()
                .filter(|a| a.is_write)
                .map(|a| a.address)
                .collect();
            
            if writers.len() > 1 {
                incidents.push(FalseSharingIncident {
                    cache_line: line,
                    addresses: writers.into_iter().collect(),
                    access_count: accesses.len(),
                });
            }
        }
        
        incidents
    }
}
```

---

### Law M-004: Store Buffer Visibility

> **"Writes may be buffered; reads see buffered values first."**

```
∀ read(addr) by core C:
    value = store_buffer(C, addr) ∨ main_memory(addr)
    where store_buffer is checked first
```

#### Store Buffer Model

```rust
/// Per-core store buffer
pub struct StoreBuffer {
    /// Pending writes (FIFO order)
    writes: VecDeque<PendingWrite>,
    
    /// Maximum buffer depth
    max_depth: usize,
    
    /// Associated core
    core_id: usize,
}

impl StoreBuffer {
    /// Check if buffered value exists for address
    pub fn lookup(&self, addr: usize, size: usize) -> Option<Vec<u8>> {
        // Search from newest to oldest (most recent write wins)
        for write in self.writes.iter().rev() {
            if write.overlaps(addr, size) {
                return Some(write.extract_value(addr, size));
            }
        }
        None
    }
    
    /// Add write to buffer
    pub fn enqueue(&mut self, addr: usize, value: Vec<u8>, ordering: MemoryOrdering) {
        // Release/SeqCst flushes first
        if matches!(ordering, MemoryOrdering::Release | MemoryOrdering::SeqCst) {
            self.flush();
        }
        
        self.writes.push_back(PendingWrite { addr, value, ordering });
        
        // Evict oldest if buffer full
        while self.writes.len() > self.max_depth {
            self.flush_oldest();
        }
    }
    
    /// Flush all pending writes to main memory
    pub fn flush(&mut self) -> Vec<PendingWrite> {
        std::mem::take(&mut self.writes).into_iter().collect()
    }
}
```

---

## 4. Scheduling Laws (The Arbiter of Fate)

### Law S-001: Progress Guarantee

> **"Runnable tasks will eventually run."**

```
∀ task ∈ Tasks:
    state(task) = Runnable ⟹ ◇(state(task) = Running)
    
    where ◇ means "eventually"
```

#### Fairness Implementation

```rust
impl SchedulerOracle {
    /// Ensure progress for all runnable tasks
    pub fn ensure_progress(&self) -> bool {
        let runnable: Vec<_> = self.tasks.iter()
            .filter(|t| t.state == TaskState::Runnable)
            .collect();
        
        // At least one task must be selected if any are runnable
        !runnable.is_empty() == self.select_next().is_some()
    }
    
    /// Check for starvation
    pub fn check_starvation(&self, max_wait_ticks: u64) -> Vec<TaskId> {
        let current_tick = self.tick_counter.load(Ordering::Acquire);
        
        self.tasks.iter()
            .filter(|t| {
                t.state == TaskState::Runnable
                && current_tick - t.last_scheduled_tick > max_wait_ticks
            })
            .map(|t| t.id)
            .collect()
    }
}
```

---

### Law S-002: Deadlock Detection

> **"Circular waits are detected and reported."**

```
Deadlock ⟺ ∃ cycle in WaitForGraph
    where WaitForGraph = {(t₁, t₂) | t₁ waits for resource held by t₂}
```

#### Wait-For Graph Analysis

```rust
impl SchedulerOracle {
    /// Build wait-for graph and detect cycles
    pub fn detect_deadlock(&self) -> Option<DeadlockReport> {
        // Build wait-for graph
        let mut wait_for: HashMap<TaskId, TaskId> = HashMap::new();
        
        for task in self.tasks.iter() {
            if let Some(BlockReason::Mutex { mutex_id }) = &task.blocked_on {
                if let Some(holder) = self.mutex_holders.get(mutex_id) {
                    wait_for.insert(task.id, *holder);
                }
            }
        }
        
        // Detect cycle using DFS with coloring
        let cycle = self.find_cycle_dfs(&wait_for)?;
        
        Some(DeadlockReport {
            cycle,
            resources: self.extract_resources(&cycle),
            timestamp: self.clock.now_ns(),
        })
    }
    
    fn find_cycle_dfs(&self, graph: &HashMap<TaskId, TaskId>) -> Option<Vec<TaskId>> {
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        let mut path = Vec::new();
        
        for &start in graph.keys() {
            if self.dfs_visit(start, graph, &mut visited, &mut rec_stack, &mut path) {
                return Some(path);
            }
        }
        
        None
    }
}
```

---

### Law S-003: Priority Inversion Detection

> **"High-priority tasks blocked by low-priority tasks are flagged."**

```
PriorityInversion ⟺ 
    ∃ t_high, t_low, resource:
        priority(t_high) > priority(t_low)
        ∧ t_high waits for resource
        ∧ t_low holds resource
```

#### Detection Implementation

```rust
#[derive(Debug)]
pub struct PriorityInversion {
    pub high_priority_task: TaskId,
    pub high_priority: u8,
    pub low_priority_holder: TaskId,
    pub low_priority: u8,
    pub resource: ResourceId,
    pub duration_ns: u64,
}

impl SchedulerOracle {
    /// Detect priority inversions
    pub fn detect_priority_inversions(&self) -> Vec<PriorityInversion> {
        let mut inversions = Vec::new();
        
        for task in self.tasks.iter() {
            if task.state != TaskState::Blocked {
                continue;
            }
            
            if let Some(resource) = task.blocked_on.as_ref().and_then(|b| b.resource()) {
                if let Some(holder_id) = self.resource_holders.get(&resource) {
                    if let Some(holder) = self.tasks.get(holder_id) {
                        if task.priority > holder.priority {
                            inversions.push(PriorityInversion {
                                high_priority_task: task.id,
                                high_priority: task.priority,
                                low_priority_holder: *holder_id,
                                low_priority: holder.priority,
                                resource,
                                duration_ns: self.clock.now_ns() - task.blocked_since_ns,
                            });
                        }
                    }
                }
            }
        }
        
        inversions
    }
}
```

---

## 5. Kernel Laws (Sovereign Compliance)

### Law K-001: Tenant Heap Isolation

> **"Each tenant's heap is bounded and isolated."**

```
∀ tenant ∈ Tenants:
    heap_usage(tenant) ≤ heap_limit(tier(tenant))
    ∧ ¬∃ addr: addr ∈ heap(tenant₁) ∧ addr ∈ heap(tenant₂) where tenant₁ ≠ tenant₂
```

#### Heap Limits by Tier

| Tier | Heap Limit | Rationale |
|------|------------|-----------|
| Free | 128 MB | Basic serverless workload |
| Standard | 256 MB | Production workload |
| Enterprise | 512 MB | Heavy computation |

#### Implementation

```rust
impl TenantHeapGuard {
    pub fn check_allocation(&self, size: usize) -> Result<(), HeapError> {
        let current = self.current_usage.load(Ordering::Acquire);
        let new_usage = current.checked_add(size)
            .ok_or(HeapError::Overflow)?;
        
        if new_usage > self.limit {
            // Trigger GC first
            self.trigger_gc();
            
            // Check again
            let after_gc = self.current_usage.load(Ordering::Acquire);
            if after_gc + size > self.limit {
                return Err(HeapError::LimitExceeded {
                    requested: size,
                    current: after_gc,
                    limit: self.limit,
                });
            }
        }
        
        Ok(())
    }
}
```

---

### Law K-002: Execution Time Watchdog

> **"Runaway execution is terminated."**

```
∀ execution ∈ Executions:
    duration(execution) > max_execution_time(tier)
    ⟹ status(execution) = Terminated
```

#### Watchdog Implementation

```rust
impl ExecutionWatchdog {
    /// Monitor execution and terminate if timeout
    pub fn watch(&self, task_id: TaskId, max_time: Duration) -> WatchdogHandle {
        let terminated = Arc::new(AtomicBool::new(false));
        let terminated_clone = terminated.clone();
        let isolate_handle = self.get_isolate_handle(task_id);
        
        // Spawn OS thread (not async - must fire regardless of event loop)
        std::thread::spawn(move || {
            std::thread::sleep(max_time);
            
            if !terminated_clone.load(Ordering::Acquire) {
                // Force termination
                isolate_handle.terminate_execution();
                terminated_clone.store(true, Ordering::Release);
            }
        });
        
        WatchdogHandle { terminated }
    }
}
```

---

### Law K-003: Cross-Tenant Isolation

> **"Tenants cannot observe or affect each other."**

```
∀ tenant₁, tenant₂ ∈ Tenants where tenant₁ ≠ tenant₂:
    ¬observable(tenant₁, state(tenant₂))
    ∧ ¬modifiable(tenant₁, state(tenant₂))
```

#### Isolation Enforcement

| Layer | Mechanism | Enforcement |
|-------|-----------|-------------|
| Memory | Separate V8 Isolates | V8 engine |
| Storage | Separate Sled Trees | `open_tree(tenant_id)` |
| File System | Path remapping | Chroot-like virtualization |
| Time | Per-tenant CPU budgets | Watchdog per tenant |

---

## 6. Invariant Summary Table

| ID | Law | Module | TLA+ Spec | Kani Proof |
|----|-----|--------|-----------|------------|
| T-001 | Temporal Monotonicity | VirtualClock | `TimeMonotonicity` | `proof_time_monotonic` |
| T-002 | Event Causality | VirtualClock | `CausalPreserved` | `proof_causality` |
| T-003 | Event Ordering | VirtualClock | `EventOrdering` | `proof_total_order` |
| T-004 | Discrete Time | VirtualClock | `DiscreteTime` | N/A |
| M-001 | Sequential Consistency | SimulatedMemory | `SeqCstOrder` | `proof_seqcst` |
| M-002 | Atomic Integrity | SimulatedMemory | `AtomicIntegrity` | `proof_atomic_cas` |
| M-003 | Cache Line Granularity | SimulatedMemory | N/A | `proof_cache_line` |
| M-004 | Store Buffer Visibility | SimulatedMemory | `StoreBufferSem` | `proof_store_buffer` |
| S-001 | Progress Guarantee | SchedulerOracle | `Progress` | `proof_progress` |
| S-002 | Deadlock Detection | SchedulerOracle | `NoDeadlock` | `proof_deadlock_detect` |
| S-003 | Priority Inversion | SchedulerOracle | N/A | `proof_priority_inversion` |
| K-001 | Heap Isolation | SovereignPool | `HeapLimit` | `proof_heap_limit` |
| K-002 | Watchdog Termination | SovereignPool | `WatchdogGuarantee` | `proof_watchdog` |
| K-003 | Tenant Isolation | SovereignPool | `TenantIsolation` | `proof_isolation` |

---

## 7. Verification Requirements

### 7.1 TLA+ Model Checking

All temporal and memory laws must pass TLC model checking with:
- Deadlock freedom
- Liveness properties (Progress, Fairness)
- Safety properties (all invariants)

### 7.2 Kani Proofs

All Rust implementations must have Kani proofs for:
- Panic freedom (no unwrap, no overflow)
- Memory safety (no out-of-bounds)
- Property verification (invariant maintenance)

### 7.3 Simulation Testing

- Minimum 1 billion events under `EventDriven` mode
- Minimum 10 million events under `Exhaustive` DPOR
- All edge cases from EDGE_CASE_MATRIX must be covered

---

*"These laws are not guidelines. They are the physics of our universe."*

— K-ACA v2.0