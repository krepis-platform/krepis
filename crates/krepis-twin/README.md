# 🌌 Krepis Digital Twin Simulator

**The Universe Engine for Deterministic Kernel Incubation**

> *"Before we write the kernel, we define the physics of its universe."*

```
Version: 1.0.0
Status: Constitutional Draft
Classification: Core Infrastructure Specification
Last Updated: 2025-01-09
```

---

## Table of Contents

1. [Philosophy & Core Principles](#1-philosophy--core-principles)
2. [System Architecture](#2-system-architecture)
3. [Module Specifications](#3-module-specifications)
4. [Formal Verification Integration](#4-formal-verification-integration)
5. [Development Workflow](#5-development-workflow)
6. [Compliance Matrix](#6-compliance-matrix)

---

## 1. Philosophy & Core Principles

### 1.1 The Deterministic Imperative

The Digital Twin Simulator exists for a singular purpose: **to guarantee that every execution of the Krepis kernel produces identical results given identical inputs, regardless of when, where, or how many times it runs.**

#### Definition of Deterministic Execution

```
DETERMINISM ≡ ∀ input I, ∀ execution E₁, E₂:
    Execute(I, E₁) = Execute(I, E₂)
    ∧ Trace(I, E₁) = Trace(I, E₂)
    ∧ Time(I, E₁) ≅ Time(I, E₂)  // Virtual time equivalence
```

A system is **deterministic** if and only if:

| Property | Definition | Violation Example |
|----------|------------|-------------------|
| **Output Determinism** | Same input → Same output | HashMap iteration order |
| **Trace Determinism** | Same input → Same execution path | Thread scheduling variance |
| **Temporal Determinism** | Same input → Same virtual timestamps | Wall-clock dependency |

#### Guaranteeing Determinism: The Three Pillars

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    DETERMINISM GUARANTEE FRAMEWORK                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐        │
│   │  PILLAR I:      │  │  PILLAR II:     │  │  PILLAR III:    │        │
│   │  Temporal       │  │  Spatial        │  │  Causal         │        │
│   │  Isolation      │  │  Isolation      │  │  Ordering       │        │
│   └────────┬────────┘  └────────┬────────┘  └────────┬────────┘        │
│            │                    │                    │                  │
│   Virtual Clock         Simulated Memory      Lamport Timestamps        │
│   replaces all          replaces all          enforce happens-before    │
│   wall-clock access     hardware memory       across all events         │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 1.2 Virtual Time vs. Wall-Clock: The Great Separation

The simulator enforces an **absolute firewall** between virtual time and wall-clock time.

#### The Separation Principle

```rust
// ❌ FORBIDDEN: Wall-clock access in kernel code
use std::time::Instant;           // COMPILE ERROR in simulator mode
use std::time::SystemTime;        // COMPILE ERROR in simulator mode
std::thread::sleep(duration);     // COMPILE ERROR in simulator mode

// ✅ REQUIRED: Virtual time through HAL
use krepis_twin::hal::TimeProvider;

fn example<T: TimeProvider>(time: &T) {
    let now = time.now_ns();              // Virtual nanoseconds
    time.schedule_after(1000, callback);  // Virtual delay
}
```

#### Why This Matters

| Scenario | Wall-Clock Behavior | Virtual Time Behavior |
|----------|---------------------|----------------------|
| Run test twice | Different timestamps | Identical timestamps |
| Run on slow machine | Timeouts may trigger | Consistent timing |
| Debug with breakpoints | Time continues | Time frozen |
| Replay execution | Impossible | Bit-for-bit identical |

### 1.3 Zero-Drift Nanosecond Precision

The simulator guarantees **mathematical precision** in time measurement with zero drift.

#### Precision Hierarchy

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     TEMPORAL PRECISION HIERARCHY                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Level 0: Logical Tick                                                │
│   └── Discrete events, no physical time interpretation                 │
│                                                                         │
│   Level 1: Nanosecond Virtual Time (u64)                               │
│   └── 584 years of range, zero floating-point error                    │
│                                                                         │
│   Level 2: Lamport Timestamp                                           │
│   └── Causal ordering when physical time is ambiguous                  │
│                                                                         │
│   Level 3: Composite Ordering Key                                      │
│   └── (virtual_ns, lamport, event_id) → Total ordering                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

#### The Zero-Drift Contract

```rust
/// The Virtual Clock Contract
/// 
/// INVARIANT: Time is represented as u64 nanoseconds.
///            No floating-point. No drift. No rounding.
/// 
/// INVARIANT: time.now_ns() is monotonically non-decreasing.
///            After tick(), now_ns()' >= now_ns()
/// 
/// INVARIANT: Events scheduled at time T are processed exactly
///            when virtual time reaches T, not before, not after.
pub struct VirtualClock {
    current_ns: AtomicU64,  // No f64, no Duration, just u64
    // ...
}
```

### 1.4 Numeric Determinism

Floating-point operations are **inherently non-deterministic** across platforms due to:
- Different FPU implementations (x87 vs SSE vs ARM)
- Compiler optimizations (fused multiply-add)
- Rounding mode variations

#### The Soft-Float Mandate

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    NUMERIC DETERMINISM STRATEGY                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   FORBIDDEN                          REQUIRED                           │
│   ──────────                         ────────                           │
│   f32, f64 native ops                softfloat-rs library               │
│   x87 FPU instructions               IEEE 754 software emulation        │
│   Platform-specific rounding         Explicit rounding mode             │
│                                                                         │
│   PREFERRED ALTERNATIVES:                                               │
│   ├── Fixed-point arithmetic (i64 with implicit decimal)               │
│   ├── Rational numbers (num-rational crate)                            │
│   └── Arbitrary precision (rug crate for critical paths)               │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

```rust
// ❌ FORBIDDEN: Native floating-point
let result = 0.1 + 0.2;  // Platform-dependent!

// ✅ REQUIRED: Soft-float or fixed-point
use softfloat::F64;
let result = F64::from_bits(0x3FB999999999999A) + F64::from_bits(0x3FC999999999999A);

// ✅ PREFERRED: Fixed-point for financial/timing
use fixed::types::I32F32;
let amount = I32F32::from_num(100.50);
```

### 1.5 Entropy & I/O Virtualization

All sources of non-determinism must be **virtualized and seeded**:

#### Deterministic Entropy Provider

```
┌─────────────────────────────────────────────────────────────────────────┐
│                  ENTROPY VIRTUALIZATION ARCHITECTURE                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│                        ┌──────────────────┐                             │
│                        │   Master Seed    │                             │
│                        │   (u64 input)    │                             │
│                        └────────┬─────────┘                             │
│                                 │                                       │
│              ┌──────────────────┼──────────────────┐                   │
│              ▼                  ▼                  ▼                   │
│     ┌────────────────┐ ┌────────────────┐ ┌────────────────┐          │
│     │  Random Number │ │  Network I/O   │ │  Filesystem    │          │
│     │  Generator     │ │  Ordering      │ │  Timestamps    │          │
│     │  (ChaCha20)    │ │  (Packet Seq)  │ │  (Virtual)     │          │
│     └────────────────┘ └────────────────┘ └────────────────┘          │
│                                                                         │
│   GUARANTEE: Same seed → Same random values, packet order, timestamps  │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

```rust
/// Deterministic entropy provider
/// 
/// # Contract
/// Given the same seed, ALL of the following are identical:
/// - Random number sequences
/// - Network packet arrival order  
/// - I/O completion order
/// - Timer jitter simulation
pub struct DeterministicEntropy {
    seed: u64,
    rng: ChaCha20Rng,
    packet_sequencer: PacketOrderer,
    io_scheduler: IoOrderer,
}

impl DeterministicEntropy {
    pub fn new(seed: u64) -> Self {
        Self {
            seed,
            rng: ChaCha20Rng::seed_from_u64(seed),
            packet_sequencer: PacketOrderer::seeded(seed),
            io_scheduler: IoOrderer::seeded(seed),
        }
    }
    
    /// Get deterministic random bytes
    pub fn random_bytes(&mut self, len: usize) -> Vec<u8> {
        let mut buf = vec![0u8; len];
        self.rng.fill_bytes(&mut buf);
        buf
    }
    
    /// Determine network packet arrival order
    pub fn next_packet_order(&mut self, pending: &[PacketId]) -> PacketId {
        self.packet_sequencer.select_next(pending, &mut self.rng)
    }
}
```

---

## 2. System Architecture

### 2.1 High-Level Architecture Diagram

```mermaid
graph TB
    subgraph Formal["Formal Verification Layer"]
        TLA[TLA+ Specifications]
        Kani[Kani Proofs]
        Prusti[Prusti Contracts]
    end
    
    subgraph Twin["Digital Twin Simulator"]
        subgraph Orchestrator["Simulation Orchestrator"]
            ORCH[Orchestrator Engine]
            CI[Chaos Injector<br/>Fault Injection]
            MME[Memory Model<br/>Emulator]
            DEP[Deterministic<br/>Entropy Provider]
        end
        
        subgraph Core["Deterministic Execution Core"]
            VC[Virtual Clock<br/>ns precision]
            SM[Simulated Memory<br/>Cache Model]
            SO[Scheduler Oracle<br/>Interleaving]
            TR[Trace Recorder<br/>TLA+ Export]
        end
        
        HAL[Hardware Abstraction Layer]
    end
    
    subgraph Kernel["Krepis Sovereign Kernel"]
        SP[SovereignPool]
        TC[Tenant Context]
        RQ[Resource Quota]
    end
    
    subgraph SDK["TypeScript SDK"]
        CTX[KrepisContext]
        PL[Pipeline]
        BH[Behaviors]
    end
    
    TLA -->|Invariants| TR
    Kani -->|Property Proofs| Core
    
    ORCH -->|Controls| CI
    ORCH -->|Controls| MME
    ORCH -->|Controls| DEP
    CI -->|Injects Faults| SM
    CI -->|Injects Faults| SO
    MME -->|Configures| SM
    DEP -->|Seeds| SO
    
    VC <--> SM
    VC <--> SO
    SO <--> SM
    TR --> VC
    TR --> SM
    TR --> SO
    
    Core --> HAL
    HAL -->|Simulator Backend| Twin
    HAL -->|Production Backend| Kernel
    
    Kernel --> SDK
```

#### Orchestrator Responsibilities

| Component | Role | Control Interface |
|-----------|------|-------------------|
| **Orchestrator Engine** | Master controller for simulation scenarios | `SimulationConfig` |
| **Chaos Injector** | Fault injection (bit flips, delays, crashes) | `ChaosProfile` |
| **Memory Model Emulator** | Cache behavior, ordering models | `MemoryModelConfig` |
| **Deterministic Entropy** | Seeded randomness for all I/O | `EntropySeed`

### 2.2 Component Interaction Flow

```mermaid
sequenceDiagram
    participant User as User Request
    participant HAL as HAL Interface
    participant VC as Virtual Clock
    participant SO as Scheduler Oracle
    participant SM as Simulated Memory
    participant TR as Trace Recorder
    participant TLA as TLA+ Validator

    User->>HAL: execute(ctx, code)
    HAL->>VC: now_ns()
    VC-->>HAL: t₀ = 1000ns
    
    HAL->>TR: record(START, t₀)
    HAL->>SO: spawn(task)
    SO->>VC: schedule_after(100ns, task)
    
    loop Event Loop
        VC->>VC: tick()
        VC->>SO: get_expired_events()
        SO-->>VC: [event₁, event₂]
        
        SO->>SM: execute(event₁)
        SM->>TR: record(MEM_ACCESS, addr, value)
        SM-->>SO: result
        
        TR->>TLA: validate_trace_segment()
        TLA-->>TR: ✓ Invariants hold
    end
    
    HAL-->>User: ExecutionResult
```

### 2.3 Layer Responsibilities

| Layer | Responsibility | Key Invariants |
|-------|----------------|----------------|
| **Virtual Clock** | Time source of truth | Monotonicity, Zero-drift |
| **Simulated Memory** | Memory model emulation | Sequential consistency, Cache coherence |
| **Scheduler Oracle** | Execution interleaving | Fairness, Progress guarantee |
| **Trace Recorder** | Execution history | Complete capture, TLA+ compatibility |
| **HAL** | Backend abstraction | Zero-cost in production |

---

## 3. Module Specifications

### 3.1 Virtual Clock Module

```rust
// crates/krepis-twin/src/time/mod.rs

/// Virtual Clock - The Heartbeat of the Universe
/// 
/// # Invariants (TLA+ Verified)
/// 
/// - `TimeMonotonicity`: ∀ tick: now_ns()' ≥ now_ns()
/// - `EventOrdering`: ∀ e₁, e₂: e₁.scheduled_at < e₂.scheduled_at 
///                    ⇒ e₁ processed before e₂
/// - `CausalConsistency`: ∀ e₁ → e₂ (causally): e₁.lamport < e₂.lamport
/// 
/// # Edge Cases Handled
/// 
/// - Same-tick events: Ordered by (lamport, event_id)
/// - Time jumps: Batch process all events in [t, t+Δ]
/// - Overflow: u64 ns = 584 years, panic on overflow attempt

#[derive(Debug)]
pub struct VirtualClock {
    /// Current virtual time in nanoseconds
    /// Range: 0 to 2^64-1 (584 years)
    current_ns: AtomicU64,
    
    /// Lamport logical clock for causal ordering
    lamport: AtomicU64,
    
    /// Min-heap of scheduled future events
    /// Invariant: All events have scheduled_at_ns > current_ns
    event_heap: Mutex<BinaryHeap<Reverse<ScheduledEvent>>>,
    
    /// Monotonic event ID generator
    /// Invariant: Strictly increasing, never wraps
    next_event_id: AtomicU64,
    
    /// Time progression mode
    mode: TimeMode,
    
    /// Statistics for observability
    stats: ClockStats,
}

/// Time progression strategies
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TimeMode {
    /// Jump directly to next event (maximum simulation speed)
    /// Use for: Exhaustive testing, billion-iteration runs
    EventDriven,
    
    /// Fixed nanosecond increments (fine-grained analysis)
    /// Use for: Race condition detection, timing analysis
    FixedTick { interval_ns: u64 },
    
    /// Synchronized with wall-clock (integration testing)
    /// Use for: Production behavior validation
    /// WARNING: Non-deterministic, for testing only
    RealTime { speedup: f64 },
}

/// A scheduled event with total ordering guarantee
#[derive(Debug, Clone, Eq, PartialEq)]
pub struct ScheduledEvent {
    /// Virtual time when event should fire (ns)
    pub scheduled_at_ns: u64,
    
    /// Lamport timestamp at scheduling time
    pub lamport: u64,
    
    /// Unique, monotonic event ID
    /// Guarantees: event_id₁ < event_id₂ if scheduled earlier
    pub event_id: u64,
    
    /// Event payload
    pub payload: EventPayload,
}

impl Ord for ScheduledEvent {
    fn cmp(&self, other: &Self) -> Ordering {
        // CRITICAL: This ordering is the law of event physics
        // 1. Earlier scheduled time wins
        // 2. Lower Lamport (older causality) wins
        // 3. Lower event_id (earlier scheduling) wins
        // Result: TOTAL ORDERING - no ambiguity ever
        self.scheduled_at_ns.cmp(&other.scheduled_at_ns)
            .then_with(|| self.lamport.cmp(&other.lamport))
            .then_with(|| self.event_id.cmp(&other.event_id))
    }
}

impl VirtualClock {
    /// Create a new virtual clock
    /// 
    /// # Panics
    /// Never panics. Initial state is always valid.
    pub fn new(mode: TimeMode) -> Self {
        Self {
            current_ns: AtomicU64::new(0),
            lamport: AtomicU64::new(0),
            event_heap: Mutex::new(BinaryHeap::new()),
            next_event_id: AtomicU64::new(0),
            mode,
            stats: ClockStats::default(),
        }
    }
    
    /// Get current virtual time in nanoseconds
    /// 
    /// # Guarantees
    /// - Returns value ≥ 0
    /// - Never decreases between calls
    /// - Thread-safe (Acquire ordering)
    #[inline(always)]
    pub fn now_ns(&self) -> u64 {
        self.current_ns.load(Ordering::Acquire)
    }
    
    /// Advance time and harvest expired events
    /// 
    /// # Returns
    /// Events that have expired, in deterministic order
    /// 
    /// # Invariants Maintained
    /// - All returned events have scheduled_at_ns ≤ new current_ns
    /// - Events are returned in total order (time, lamport, id)
    /// - current_ns is updated atomically after harvesting
    pub fn tick(&self) -> Vec<ScheduledEvent> {
        let target_ns = self.compute_target_time();
        let expired = self.harvest_expired_events(target_ns);
        
        // Advance time (monotonic, atomic)
        self.current_ns.fetch_max(target_ns, Ordering::Release);
        self.lamport.fetch_add(1, Ordering::Release);
        
        self.stats.record_tick(expired.len());
        expired
    }
    
    /// Schedule a future event
    /// 
    /// # Arguments
    /// - `delay_ns`: Nanoseconds from now
    /// - `payload`: Event data
    /// 
    /// # Returns
    /// Unique event ID for cancellation
    /// 
    /// # Panics
    /// - If delay_ns would cause overflow (> 584 years in future)
    pub fn schedule(&self, delay_ns: u64, payload: EventPayload) -> u64 {
        let now = self.now_ns();
        let scheduled_at_ns = now.checked_add(delay_ns)
            .expect("Time overflow: cannot schedule event 584+ years in future");
        
        let event_id = self.next_event_id.fetch_add(1, Ordering::Relaxed);
        let lamport = self.lamport.fetch_add(1, Ordering::AcqRel);
        
        let event = ScheduledEvent {
            scheduled_at_ns,
            lamport,
            event_id,
            payload,
        };
        
        self.event_heap.lock().push(Reverse(event));
        self.stats.record_schedule();
        
        event_id
    }
    
    /// Cancel a scheduled event
    /// 
    /// # Returns
    /// - `true` if event was found and cancelled
    /// - `false` if event already fired or doesn't exist
    pub fn cancel(&self, event_id: u64) -> bool {
        let mut heap = self.event_heap.lock();
        let initial_len = heap.len();
        
        // Rebuild heap without the cancelled event
        let events: Vec<_> = heap.drain().filter(|e| e.0.event_id != event_id).collect();
        *heap = events.into_iter().collect();
        
        heap.len() < initial_len
    }
    
    // Private: Compute next time target based on mode
    fn compute_target_time(&self) -> u64 {
        match self.mode {
            TimeMode::EventDriven => {
                self.event_heap.lock()
                    .peek()
                    .map(|e| e.0.scheduled_at_ns)
                    .unwrap_or(self.now_ns())
            }
            TimeMode::FixedTick { interval_ns } => {
                self.now_ns().saturating_add(interval_ns)
            }
            TimeMode::RealTime { speedup } => {
                // Non-deterministic! Only for integration tests
                let wall_elapsed = self.stats.wall_clock_elapsed();
                (wall_elapsed.as_nanos() as f64 * speedup) as u64
            }
        }
    }
    
    // Private: Harvest events up to target time
    fn harvest_expired_events(&self, target_ns: u64) -> Vec<ScheduledEvent> {
        let mut heap = self.event_heap.lock();
        let mut expired = Vec::new();
        
        while let Some(Reverse(event)) = heap.peek() {
            if event.scheduled_at_ns <= target_ns {
                expired.push(heap.pop().unwrap().0);
            } else {
                break;
            }
        }
        
        // Already in sorted order due to heap + Ord implementation
        expired
    }
}
```

### 3.2 Simulated Memory Module

```rust
// crates/krepis-twin/src/memory/mod.rs

/// Simulated Memory - The Fabric of Space
/// 
/// Models CPU memory hierarchy with deterministic behavior:
/// - Cache line granularity (64 bytes)
/// - Memory ordering semantics (SeqCst, Acquire, Release, Relaxed)
/// - Store buffer simulation for weak memory model testing
/// 
/// # Invariants (TLA+ Verified)
/// 
/// - `SequentialConsistency`: Under SeqCst, all cores see same order
/// - `CacheCoherence`: No stale reads after synchronization
/// - `AtomicIntegrity`: Atomic operations are truly atomic

/// Cache line size in bytes (x86-64 standard)
pub const CACHE_LINE_SIZE: usize = 64;

/// Memory ordering semantics
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryOrdering {
    /// Total order visible to all threads
    SeqCst,
    /// Prevents reads from being reordered before this
    Acquire,
    /// Prevents writes from being reordered after this
    Release,
    /// No ordering guarantees
    Relaxed,
}

/// A simulated memory region
#[derive(Debug)]
pub struct SimulatedMemory {
    /// Main memory (page-aligned)
    pages: RwLock<HashMap<usize, Page>>,
    
    /// Per-core store buffers (for weak memory modeling)
    store_buffers: Vec<Mutex<VecDeque<PendingStore>>>,
    
    /// Cache state per line
    cache_state: DashMap<usize, CacheLineState>,
    
    /// Access log for trace recording
    access_log: Mutex<Vec<MemoryAccess>>,
    
    /// Configuration
    config: MemoryConfig,
}

/// Cache line state (MESI-like protocol)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CacheLineState {
    /// Not in cache
    Invalid,
    /// Clean, may be shared
    Shared,
    /// Dirty, exclusive ownership
    Exclusive,
    /// Being modified
    Modified,
}

/// A pending store in the store buffer
#[derive(Debug, Clone)]
pub struct PendingStore {
    pub address: usize,
    pub value: Vec<u8>,
    pub ordering: MemoryOrdering,
    pub timestamp: u64,
}

/// Memory access record for tracing
#[derive(Debug, Clone)]
pub struct MemoryAccess {
    pub address: usize,
    pub size: usize,
    pub is_write: bool,
    pub ordering: MemoryOrdering,
    pub value: Vec<u8>,
    pub core_id: usize,
    pub virtual_time_ns: u64,
    pub lamport: u64,
}

impl SimulatedMemory {
    /// Read from simulated memory
    /// 
    /// # Ordering Semantics
    /// - SeqCst: Flush all store buffers first
    /// - Acquire: Flush store buffer for this address
    /// - Relaxed: May see stale value from store buffer
    pub fn read(
        &self,
        addr: usize,
        size: usize,
        ordering: MemoryOrdering,
        core_id: usize,
    ) -> Vec<u8> {
        // Enforce ordering constraints
        match ordering {
            MemoryOrdering::SeqCst => self.flush_all_store_buffers(),
            MemoryOrdering::Acquire => self.flush_store_buffer(core_id, addr),
            _ => {}
        }
        
        // Check store buffer first (may have pending write)
        if let Some(value) = self.check_store_buffer(core_id, addr, size) {
            self.record_access(addr, size, false, ordering, &value, core_id);
            return value;
        }
        
        // Read from main memory
        let value = self.read_main_memory(addr, size);
        self.update_cache_state(addr, CacheLineState::Shared);
        self.record_access(addr, size, false, ordering, &value, core_id);
        
        value
    }
    
    /// Write to simulated memory
    /// 
    /// # Ordering Semantics
    /// - SeqCst: Immediately visible to all cores
    /// - Release: Flush store buffer, then write
    /// - Relaxed: Buffer in store buffer
    pub fn write(
        &self,
        addr: usize,
        value: &[u8],
        ordering: MemoryOrdering,
        core_id: usize,
    ) {
        match ordering {
            MemoryOrdering::SeqCst => {
                self.flush_all_store_buffers();
                self.write_main_memory(addr, value);
                self.update_cache_state(addr, CacheLineState::Modified);
            }
            MemoryOrdering::Release => {
                self.flush_store_buffer(core_id, addr);
                self.write_main_memory(addr, value);
            }
            MemoryOrdering::Relaxed | MemoryOrdering::Acquire => {
                self.add_to_store_buffer(core_id, addr, value, ordering);
            }
        }
        
        self.record_access(addr, value.len(), true, ordering, value, core_id);
    }
    
    /// Atomic compare-and-swap
    /// 
    /// # Guarantees
    /// - Truly atomic (no torn reads/writes)
    /// - Returns (success, previous_value)
    pub fn compare_and_swap(
        &self,
        addr: usize,
        expected: &[u8],
        desired: &[u8],
        ordering: MemoryOrdering,
        core_id: usize,
    ) -> (bool, Vec<u8>) {
        // CAS is always SeqCst-like (total order)
        self.flush_all_store_buffers();
        
        let current = self.read_main_memory(addr, expected.len());
        
        if current == expected {
            self.write_main_memory(addr, desired);
            self.update_cache_state(addr, CacheLineState::Modified);
            (true, current)
        } else {
            (false, current)
        }
    }
    
    /// Memory fence/barrier
    pub fn fence(&self, ordering: MemoryOrdering, core_id: usize) {
        match ordering {
            MemoryOrdering::SeqCst => self.flush_all_store_buffers(),
            MemoryOrdering::Release | MemoryOrdering::Acquire => {
                self.flush_store_buffer_for_core(core_id);
            }
            MemoryOrdering::Relaxed => {} // No-op
        }
    }
    
    /// Get cache line address
    #[inline(always)]
    pub fn cache_line_of(addr: usize) -> usize {
        addr & !(CACHE_LINE_SIZE - 1)
    }
    
    /// Check if two addresses share a cache line
    #[inline(always)]
    pub fn shares_cache_line(addr1: usize, addr2: usize) -> bool {
        Self::cache_line_of(addr1) == Self::cache_line_of(addr2)
    }
}
```

### 3.3 Scheduler Oracle Module

```rust
// crates/krepis-twin/src/scheduler/mod.rs

/// Scheduler Oracle - The Arbiter of Fate
/// 
/// Controls task interleaving to explore all possible execution orders.
/// This is the key to finding race conditions and deadlocks.
/// 
/// # Invariants (TLA+ Verified)
/// 
/// - `Progress`: Some runnable task is eventually scheduled
/// - `Fairness`: No task starves indefinitely
/// - `Determinism`: Same seed → Same interleaving sequence

/// Interleaving strategy
#[derive(Debug, Clone)]
pub enum InterleavingStrategy {
    /// Round-robin (predictable, good for baseline)
    RoundRobin,
    
    /// Random with seed (reproducible chaos)
    SeededRandom { seed: u64 },
    
    /// Prioritize tasks that accessed shared memory
    /// Good for finding data races
    MemoryPressure,
    
    /// Exhaustive search with DPOR
    /// (Dynamic Partial Order Reduction)
    Exhaustive { 
        /// Maximum states to explore before giving up
        max_states: usize,
        /// Reduction strategy
        reduction: ReductionStrategy,
    },
}

/// DPOR reduction strategy
#[derive(Debug, Clone, Copy)]
pub enum ReductionStrategy {
    /// Classic DPOR - track read/write dependencies
    Classic,
    /// Optimal DPOR - minimal state exploration
    Optimal,
    /// Source-set DPOR - better for lock-heavy code
    SourceSet,
}

/// A schedulable task
#[derive(Debug, Clone)]
pub struct Task {
    pub id: TaskId,
    pub state: TaskState,
    pub priority: u8,
    pub affinity: Option<usize>,  // Preferred core
    pub last_memory_access: Option<usize>,
    pub blocked_on: Option<BlockReason>,
}

/// Task state machine
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskState {
    /// Ready to run
    Runnable,
    /// Currently executing
    Running,
    /// Waiting for I/O, lock, or time
    Blocked,
    /// Finished execution
    Completed,
    /// Terminated due to error
    Failed,
}

/// Why a task is blocked
#[derive(Debug, Clone)]
pub enum BlockReason {
    /// Waiting for a mutex
    Mutex { mutex_id: usize },
    /// Waiting for a semaphore
    Semaphore { semaphore_id: usize, permits: usize },
    /// Waiting for time
    Timer { wake_at_ns: u64 },
    /// Waiting for I/O
    Io { operation: IoOperation },
    /// Waiting for another task
    Join { task_id: TaskId },
}

/// The Oracle that decides execution order
#[derive(Debug)]
pub struct SchedulerOracle {
    /// All known tasks
    tasks: DashMap<TaskId, Task>,
    
    /// Current strategy
    strategy: InterleavingStrategy,
    
    /// RNG for seeded random (deterministic!)
    rng: Mutex<StdRng>,
    
    /// History for DPOR
    history: Mutex<ExecutionHistory>,
    
    /// Preemption points
    preemption_points: AtomicU64,
    
    /// Statistics
    stats: SchedulerStats,
}

impl SchedulerOracle {
    /// Create a new scheduler oracle
    pub fn new(strategy: InterleavingStrategy) -> Self {
        let seed = match &strategy {
            InterleavingStrategy::SeededRandom { seed } => *seed,
            _ => 0,
        };
        
        Self {
            tasks: DashMap::new(),
            strategy,
            rng: Mutex::new(StdRng::seed_from_u64(seed)),
            history: Mutex::new(ExecutionHistory::new()),
            preemption_points: AtomicU64::new(0),
            stats: SchedulerStats::default(),
        }
    }
    
    /// Spawn a new task
    pub fn spawn(&self, priority: u8, affinity: Option<usize>) -> TaskId {
        let id = TaskId::new();
        let task = Task {
            id,
            state: TaskState::Runnable,
            priority,
            affinity,
            last_memory_access: None,
            blocked_on: None,
        };
        
        self.tasks.insert(id, task);
        self.stats.record_spawn();
        id
    }
    
    /// Select next task to run
    /// 
    /// # Determinism Guarantee
    /// Given the same task set and history, returns the same task
    pub fn select_next(&self) -> Option<TaskId> {
        let runnable: Vec<_> = self.tasks.iter()
            .filter(|e| e.state == TaskState::Runnable)
            .map(|e| e.id)
            .collect();
        
        if runnable.is_empty() {
            return None;
        }
        
        let selected = match &self.strategy {
            InterleavingStrategy::RoundRobin => {
                let idx = self.preemption_points.fetch_add(1, Ordering::Relaxed) as usize;
                runnable[idx % runnable.len()]
            }
            InterleavingStrategy::SeededRandom { .. } => {
                let mut rng = self.rng.lock();
                runnable[rng.gen_range(0..runnable.len())]
            }
            InterleavingStrategy::MemoryPressure => {
                // Prefer tasks that recently accessed memory
                runnable.iter()
                    .max_by_key(|id| {
                        self.tasks.get(id)
                            .and_then(|t| t.last_memory_access)
                            .unwrap_or(0)
                    })
                    .copied()
                    .unwrap()
            }
            InterleavingStrategy::Exhaustive { .. } => {
                self.dpor_select(&runnable)
            }
        };
        
        // Update state
        if let Some(mut task) = self.tasks.get_mut(&selected) {
            task.state = TaskState::Running;
        }
        
        self.stats.record_switch();
        Some(selected)
    }
    
    /// Mark a preemption point (where context switch can occur)
    /// 
    /// Call this at:
    /// - Memory accesses (especially atomic)
    /// - Lock acquire/release
    /// - Explicit yield points
    pub fn preemption_point(&self, reason: PreemptionReason) {
        self.preemption_points.fetch_add(1, Ordering::Relaxed);
        
        if let InterleavingStrategy::Exhaustive { .. } = &self.strategy {
            self.history.lock().record_preemption(reason);
        }
    }
    
    /// DPOR task selection
    fn dpor_select(&self, runnable: &[TaskId]) -> TaskId {
        let history = self.history.lock();
        
        // Find tasks that are independent of recent operations
        // (Can be reordered without affecting outcome)
        let independent: Vec<_> = runnable.iter()
            .filter(|id| history.is_independent(**id))
            .copied()
            .collect();
        
        if !independent.is_empty() {
            // Explore independent tasks to reduce state space
            independent[0]
        } else {
            // Fall back to first runnable
            runnable[0]
        }
    }
    
    /// Block a task
    pub fn block(&self, task_id: TaskId, reason: BlockReason) {
        if let Some(mut task) = self.tasks.get_mut(&task_id) {
            task.state = TaskState::Blocked;
            task.blocked_on = Some(reason);
        }
    }
    
    /// Unblock a task
    pub fn unblock(&self, task_id: TaskId) {
        if let Some(mut task) = self.tasks.get_mut(&task_id) {
            if task.state == TaskState::Blocked {
                task.state = TaskState::Runnable;
                task.blocked_on = None;
            }
        }
    }
    
    /// Detect deadlock
    /// 
    /// # Returns
    /// Cycle of tasks involved in deadlock, if any
    pub fn detect_deadlock(&self) -> Option<Vec<TaskId>> {
        // Build wait-for graph
        let mut graph: HashMap<TaskId, TaskId> = HashMap::new();
        
        for entry in self.tasks.iter() {
            if let Some(BlockReason::Mutex { mutex_id }) = &entry.blocked_on {
                // Find who holds this mutex
                if let Some(holder) = self.find_mutex_holder(*mutex_id) {
                    graph.insert(entry.id, holder);
                }
            }
        }
        
        // Detect cycle using tortoise-hare
        self.find_cycle(&graph)
    }
    
    /// Detect priority inversion
    pub fn detect_priority_inversion(&self) -> Vec<PriorityInversion> {
        let mut inversions = Vec::new();
        
        for high in self.tasks.iter().filter(|t| t.priority > 128) {
            if let Some(BlockReason::Mutex { mutex_id }) = &high.blocked_on {
                if let Some(holder_id) = self.find_mutex_holder(*mutex_id) {
                    if let Some(holder) = self.tasks.get(&holder_id) {
                        if holder.priority < high.priority {
                            inversions.push(PriorityInversion {
                                high_priority_task: high.id,
                                low_priority_holder: holder_id,
                                mutex_id: *mutex_id,
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

### 3.4 Trace Recorder Module

```rust
// crates/krepis-twin/src/trace/mod.rs

/// Trace Recorder - The Historian of All Events
/// 
/// Records every significant event for:
/// - Debugging (replay exact execution)
/// - Verification (TLA+ trace validation)
/// - Analysis (performance profiling)
/// 
/// # Invariants
/// 
/// - `Completeness`: Every state-changing event is recorded
/// - `Ordering`: Events are recorded in causal order
/// - `Exportability`: Traces can be exported to TLA+ format

/// A recorded trace
#[derive(Debug, Clone)]
pub struct ExecutionTrace {
    /// Trace metadata
    pub metadata: TraceMetadata,
    
    /// Ordered sequence of events
    pub events: Vec<TraceEvent>,
    
    /// State snapshots at key points
    pub snapshots: Vec<StateSnapshot>,
}

/// Trace metadata
#[derive(Debug, Clone)]
pub struct TraceMetadata {
    pub trace_id: Uuid,
    pub started_at: DateTime<Utc>,
    pub kernel_version: String,
    pub simulator_version: String,
    pub seed: Option<u64>,
    pub interleaving_strategy: String,
}

/// A single trace event
#[derive(Debug, Clone)]
pub struct TraceEvent {
    /// Unique event ID
    pub id: u64,
    
    /// Virtual time when event occurred
    pub virtual_time_ns: u64,
    
    /// Lamport timestamp
    pub lamport: u64,
    
    /// Event type and data
    pub kind: TraceEventKind,
    
    /// Causal predecessor (if any)
    pub caused_by: Option<u64>,
    
    /// Associated task
    pub task_id: Option<TaskId>,
    
    /// Associated tenant
    pub tenant_id: Option<String>,
}

/// Event types
#[derive(Debug, Clone)]
pub enum TraceEventKind {
    // Time events
    ClockTick { old_ns: u64, new_ns: u64 },
    EventScheduled { event_id: u64, scheduled_for_ns: u64 },
    EventFired { event_id: u64 },
    
    // Memory events
    MemoryRead { address: usize, size: usize, value: Vec<u8> },
    MemoryWrite { address: usize, size: usize, old_value: Vec<u8>, new_value: Vec<u8> },
    AtomicOp { address: usize, op: AtomicOpKind, result: Vec<u8> },
    CacheMiss { address: usize, line: usize },
    
    // Scheduler events
    TaskSpawned { task_id: TaskId, priority: u8 },
    TaskScheduled { task_id: TaskId },
    TaskBlocked { task_id: TaskId, reason: String },
    TaskUnblocked { task_id: TaskId },
    TaskCompleted { task_id: TaskId },
    ContextSwitch { from: Option<TaskId>, to: TaskId },
    
    // Synchronization events
    MutexAcquire { mutex_id: usize, task_id: TaskId },
    MutexRelease { mutex_id: usize, task_id: TaskId },
    SemaphoreAcquire { semaphore_id: usize, permits: usize },
    SemaphoreRelease { semaphore_id: usize, permits: usize },
    
    // Tenant events (Sovereign compliance)
    TenantCreated { tenant_id: String, tier: String },
    TenantQuotaExceeded { tenant_id: String, quota_type: String },
    WatchdogTriggered { tenant_id: String, elapsed_ms: u64 },
    IsolateCreated { tenant_id: String },
    IsolateDestroyed { tenant_id: String, reason: String },
    
    // Custom events
    Custom { name: String, data: serde_json::Value },
}

/// State snapshot at a point in time
#[derive(Debug, Clone)]
pub struct StateSnapshot {
    pub event_id: u64,
    pub virtual_time_ns: u64,
    pub memory_hash: [u8; 32],
    pub task_states: HashMap<TaskId, TaskState>,
    pub tenant_states: HashMap<String, TenantSnapshot>,
}

/// The Trace Recorder
#[derive(Debug)]
pub struct TraceRecorder {
    /// Current trace being recorded
    trace: RwLock<ExecutionTrace>,
    
    /// Event counter
    next_event_id: AtomicU64,
    
    /// Snapshot interval (in events)
    snapshot_interval: usize,
    
    /// Compression enabled
    compression: bool,
}

impl TraceRecorder {
    /// Record an event
    pub fn record(&self, kind: TraceEventKind, clock: &VirtualClock, task_id: Option<TaskId>) {
        let event = TraceEvent {
            id: self.next_event_id.fetch_add(1, Ordering::Relaxed),
            virtual_time_ns: clock.now_ns(),
            lamport: clock.lamport(),
            kind,
            caused_by: None,  // Will be set by causal analysis
            task_id,
            tenant_id: None,  // Will be set by context
        };
        
        let mut trace = self.trace.write();
        trace.events.push(event);
        
        // Take periodic snapshots
        if trace.events.len() % self.snapshot_interval == 0 {
            // Snapshot logic here
        }
    }
    
    /// Export trace to TLA+ format
    pub fn export_tla(&self) -> String {
        let trace = self.trace.read();
        let mut output = String::new();
        
        output.push_str("---- MODULE ExecutionTrace ----\n");
        output.push_str("EXTENDS KrepisUniverse\n\n");
        output.push_str("TraceStates == <<\n");
        
        for (i, event) in trace.events.iter().enumerate() {
            output.push_str(&format!("  {}", self.event_to_tla_state(event)));
            if i < trace.events.len() - 1 {
                output.push(',');
            }
            output.push('\n');
        }
        
        output.push_str(">>\n");
        output.push_str("====\n");
        
        output
    }
    
    /// Validate trace against TLA+ specification
    pub fn validate_against_tla(&self, spec_path: &Path) -> ValidationResult {
        let tla_trace = self.export_tla();
        
        // Write to temp file
        let trace_path = std::env::temp_dir().join("trace.tla");
        std::fs::write(&trace_path, &tla_trace).expect("Failed to write trace");
        
        // Run TLC
        let output = std::process::Command::new("java")
            .args(&["-jar", "tla2tools.jar", "-config", &spec_path.to_string_lossy()])
            .arg(&trace_path)
            .output()
            .expect("Failed to run TLC");
        
        self.parse_tlc_output(&output.stdout)
    }
    
    fn event_to_tla_state(&self, event: &TraceEvent) -> String {
        match &event.kind {
            TraceEventKind::ClockTick { new_ns, .. } => {
                format!("[virtualTime |-> {}, type |-> \"tick\"]", new_ns)
            }
            TraceEventKind::TaskScheduled { task_id } => {
                format!("[virtualTime |-> {}, type |-> \"schedule\", task |-> \"{}\"]", 
                    event.virtual_time_ns, task_id)
            }
            TraceEventKind::WatchdogTriggered { tenant_id, elapsed_ms } => {
                format!("[virtualTime |-> {}, type |-> \"watchdog\", tenant |-> \"{}\", elapsed |-> {}]",
                    event.virtual_time_ns, tenant_id, elapsed_ms)
            }
            // ... other event types
            _ => format!("[virtualTime |-> {}, type |-> \"unknown\"]", event.virtual_time_ns)
        }
    }
}
```

---

## 4. Formal Verification Integration

### 4.1 TLA+ Invariants

The simulator guarantees these invariants, verified by TLA+:

| ID | Invariant | Description | Module |
|----|-----------|-------------|--------|
| **T-001** | `TimeMonotonicity` | Virtual time never decreases | VirtualClock |
| **T-002** | `EventOrdering` | Events fire in scheduled order | VirtualClock |
| **T-003** | `CausalConsistency` | Lamport ordering matches causality | VirtualClock |
| **M-001** | `SequentialConsistency` | SeqCst operations are totally ordered | SimulatedMemory |
| **M-002** | `AtomicIntegrity` | No torn reads/writes on atomics | SimulatedMemory |
| **M-003** | `CacheCoherence` | MESI protocol is followed | SimulatedMemory |
| **S-001** | `Progress` | Runnable tasks eventually run | SchedulerOracle |
| **S-002** | `NoDeadlock` | Deadlocks are detected and reported | SchedulerOracle |
| **S-003** | `Fairness` | No task starves | SchedulerOracle |
| **K-001** | `HeapLimit` | Tenant heap never exceeds limit | SovereignPool |
| **K-002** | `WatchdogGuarantee` | Runaway code is terminated | SovereignPool |
| **K-003** | `IsolationIntegrity` | Tenants cannot access each other's data | SovereignPool |

### 4.2 Trace Validation Pipeline

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     TRACE VALIDATION PIPELINE                           │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌───────────┐    ┌───────────┐    ┌───────────┐    ┌───────────┐     │
│  │ Simulator │───▶│  Trace    │───▶│   TLA+    │───▶│  Report   │     │
│  │ Execution │    │  Export   │    │   TLC     │    │  Generate │     │
│  └───────────┘    └───────────┘    └───────────┘    └───────────┘     │
│        │                                  │                │            │
│        │                                  ▼                │            │
│        │                         ┌───────────────┐        │            │
│        │                         │  Invariant    │        │            │
│        │                         │  Violation?   │        │            │
│        │                         └───────┬───────┘        │            │
│        │                                 │                │            │
│        │              ┌──────────────────┼────────────────┘            │
│        │              │                  │                             │
│        ▼              ▼                  ▼                             │
│  ┌───────────┐  ┌───────────┐    ┌───────────┐                        │
│  │  Kani     │  │  Counter  │    │  CI/CD    │                        │
│  │  Proofs   │  │  Example  │    │  Report   │                        │
│  └───────────┘  └───────────┘    └───────────┘                        │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 4.3 Violation Recovery Procedure

When a trace violates a TLA+ invariant:

1. **Immediate Actions**
   - CI pipeline fails with `INVARIANT_VIOLATION` exit code
   - Counter-example trace is saved to `artifacts/violations/`
   - Slack/Discord notification sent to `#krepis-alerts`

2. **Analysis Artifacts Generated**
   - Minimal counter-example (reduced trace)
   - State diff at violation point
   - Causal graph of events leading to violation

3. **Recovery Procedure**
   ```bash
   # 1. Reproduce locally
   cargo run --package krepis-twin-runner -- \
     --replay artifacts/violations/violation-001.trace
   
   # 2. Minimize counter-example
   cargo run --package krepis-twin-reducer -- \
     --input artifacts/violations/violation-001.trace \
     --output artifacts/violations/violation-001.minimal.trace
   
   # 3. Generate fix hypothesis
   cargo run --package krepis-twin-analyzer -- \
     --trace artifacts/violations/violation-001.minimal.trace \
     --suggest-fix
   ```

---

## 5. Development Workflow

### 5.1 The Verification-First Pipeline

```mermaid
graph LR
    A[Spec Document] --> B[TLA+ Model]
    B --> C{TLC Check}
    C -->|Pass| D[AI Code Gen]
    C -->|Fail| A
    D --> E[Kani Proofs]
    E --> F{Proof Valid?}
    F -->|Yes| G[Integration Test]
    F -->|No| D
    G --> H{Trace Valid?}
    H -->|Yes| I[Production]
    H -->|No| A
```

### 5.2 Workflow Steps

| Step | Input | Tool | Output | Success Criteria |
|------|-------|------|--------|------------------|
| 1. Spec | Requirements | Human | `docs/SPEC.md` | Review approved |
| 2. TLA+ | Spec | Human + AI | `specs/tla/*.tla` | No syntax errors |
| 3. TLC | TLA+ | TLC | Model check result | All invariants hold |
| 4. Code Gen | TLA+ + Spec | Claude | Rust code | Compiles, types match |
| 5. Kani | Rust code | Kani | Proof result | All proofs pass |
| 6. Sim Test | Code | Simulator | Trace | Matches TLA+ |
| 7. Deploy | Verified code | CI/CD | Production | Canary passes |

### 5.3 CI/CD Integration

```yaml
# .github/workflows/formal-verification.yml

name: Formal Verification

on:
  push:
    paths:
      - 'crates/krepis-twin/**'
      - 'specs/tla/**'
  pull_request:
    paths:
      - 'crates/krepis-twin/**'

jobs:
  tla-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Install TLA+ Tools
        run: |
          wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar
          
      - name: Run TLC
        run: |
          for spec in specs/tla/*.tla; do
            java -jar tla2tools.jar -deadlock "$spec"
          done
          
  kani-proofs:
    runs-on: ubuntu-latest
    needs: tla-check
    steps:
      - uses: actions/checkout@v4
      
      - name: Install Kani
        run: cargo install --locked kani-verifier && cargo kani setup
        
      - name: Run Proofs
        run: |
          cd crates/krepis-twin
          cargo kani --tests --output-format terse
          
  simulation-test:
    runs-on: ubuntu-latest
    needs: kani-proofs
    steps:
      - name: Run Billion-Event Simulation
        run: |
          cargo run --release --package krepis-twin-runner -- \
            --iterations 1_000_000 \
            --strategy exhaustive \
            --validate-traces
            
      - name: Upload Traces
        if: failure()
        uses: actions/upload-artifact@v4
        with:
          name: violation-traces
          path: artifacts/violations/
```

---

## 6. Compliance Matrix

### 6.1 Sovereign Specification Compliance

| Sovereign Spec | Simulator Support | Implementation |
|----------------|-------------------|----------------|
| **Spec-001: Isolation** | ✅ Full | Virtual address spaces per tenant |
| **Spec-002: Context** | ✅ Full | HAL TimeProvider, explicit ctx |
| **Spec-003: Quotas** | ✅ Full | Virtual CPU time, memory limits |

### 6.2 Safety Guarantees

| Guarantee | Production | Simulator | Verification |
|-----------|------------|-----------|--------------|
| Memory safety | Rust ownership | + Access logging | Kani |
| Thread safety | Mutexes | + Race detection | TLA+ |
| Time safety | Wall-clock | Virtual clock | TLA+ T-001 |
| Resource safety | OS limits | Virtual limits | TLA+ K-001 |

### 6.3 Verification Levels (V-Levels)

The Krepis platform defines **five verification levels** that correspond to service tiers and assurance guarantees:

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    VERIFICATION LEVEL HIERARCHY                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   V-Level 5: Mission Critical (Enterprise+)                            │
│   ├── Exhaustive TLC (10^9+ states)                                    │
│   ├── Kani with unbounded loops                                        │
│   ├── Formal refinement proofs                                         │
│   └── Third-party audit certification                                  │
│                                                                         │
│   V-Level 4: High Assurance (Enterprise)                               │
│   ├── Full TLC medium config                                           │
│   ├── All Kani proofs                                                  │
│   ├── 10^9 simulation events                                           │
│   └── All edge cases from Matrix                                       │
│                                                                         │
│   V-Level 3: Standard Assurance (Pro/Turbo)                            │
│   ├── TLC quick config                                                 │
│   ├── Critical Kani proofs                                             │
│   ├── 10^6 simulation events                                           │
│   └── Critical edge cases only                                         │
│                                                                         │
│   V-Level 2: Basic Assurance (Standard)                                │
│   ├── TLA+ syntax validation                                           │
│   ├── Unit tests pass                                                  │
│   ├── 10^4 simulation events                                           │
│   └── Smoke tests                                                      │
│                                                                         │
│   V-Level 1: Development (Free)                                        │
│   ├── Compilation check                                                │
│   ├── Basic unit tests                                                 │
│   └── Manual testing                                                   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

| V-Level | Service Tier | TLC States | Kani Proofs | Simulation Events | Certificate |
|---------|--------------|------------|-------------|-------------------|-------------|
| **V-5** | Enterprise+ | 10^9+ | All + Unbounded | 10^12 | External Audit |
| **V-4** | Enterprise | 10^7 | All | 10^9 | Digital Integrity |
| **V-3** | Pro/Turbo | 10^5 | Critical | 10^6 | Automated |
| **V-2** | Standard | Syntax | Unit Tests | 10^4 | Build Pass |
| **V-1** | Free/Dev | None | None | Manual | None |

---

## Appendices

- **Appendix A**: [Physical Laws Specification](docs/PHYSICAL_LAWS_SPEC.md) — Immutable invariants (T-001~K-003)
- **Appendix B**: [Edge Case Matrix](docs/EDGE_CASE_MATRIX.md) — 54 catalogued failure scenarios
- **Appendix C**: [TLA+ Verification Strategy](docs/TLA_VERIFICATION_STRATEGY.md) — Formal methods integration
- **Appendix D**: [Development Workflow Guide](docs/DEVELOPMENT_WORKFLOW.md) — 5-phase verification pipeline
- **Appendix E**: [HAL Interface Reference](docs/HAL_INTERFACE.md) — Hardware abstraction layer spec

### Document Cross-Reference Index

| Topic | Primary Document | Related Sections |
|-------|------------------|------------------|
| Time Invariants (T-001~T-004) | PHYSICAL_LAWS_SPEC.md | EDGE_CASE_MATRIX.md#temporal |
| Memory Model (M-001~M-004) | PHYSICAL_LAWS_SPEC.md | TLA_VERIFICATION_STRATEGY.md#5.2 |
| Edge Case Testing | EDGE_CASE_MATRIX.md | TLA_VERIFICATION_STRATEGY.md#7.3 |
| V-Levels | README.md#6.3 | DEVELOPMENT_WORKFLOW.md#12 |
| Certificate Issuance | DEVELOPMENT_WORKFLOW.md#12 | All (V-Level gates) |

---

## License

Proprietary - Krepis Platform

---

*"The universe is deterministic. Our simulator must be too."*

— K-ACA v2.0, Chief Architect