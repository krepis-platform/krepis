# 🎯 Edge Case Matrix

**Comprehensive Failure Scenarios and Edge Case Catalog**

```
Document: EDGE_CASE_MATRIX
Version: 1.0.0
Status: Constitutional
Classification: Test Requirements Specification
```

---

## 1. Overview

This document catalogs every known edge case, failure scenario, and boundary condition that the Digital Twin Simulator must handle correctly. Each entry includes:

- **Scenario ID**: Unique identifier
- **Category**: Temporal, Spatial, Scheduling, Hardware, or Kernel
- **Description**: What can go wrong
- **Expected Behavior**: How the simulator must respond
- **Test Strategy**: How to verify correct handling
- **TLA+ Coverage**: Which invariant verifies this

---

## 2. Temporal Edge Cases

### Category: Time Flow Anomalies

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **T-EC-001** | Same-Tick Events | Multiple events scheduled for identical nanosecond | Order by (lamport, event_id) deterministically | Schedule 1000 events at t=0, verify order is reproducible |
| **T-EC-002** | Zero-Delay Schedule | `schedule(0, payload)` - immediate execution | Event fires on next tick, not current | Schedule with delay=0, assert fires after current tick completes |
| **T-EC-003** | Time Overflow Attempt | Schedule event 585+ years in future | Panic with clear error message | `schedule(u64::MAX, _)` must panic |
| **T-EC-004** | Massive Time Jump | EventDriven mode jumps 10^12 ns | All intermediate events fire in order | Schedule events at 1ns, 10^6ns, 10^12ns; verify order |
| **T-EC-005** | Event Cancellation Race | Cancel event while tick() is processing it | Either fires or doesn't, no partial state | Concurrent cancel and tick in tight loop |
| **T-EC-006** | Empty Event Queue | tick() with no scheduled events | Time unchanged, empty result | `tick()` on fresh clock returns `[]` |
| **T-EC-007** | Lamport Counter Overflow | 2^64 events scheduled | Panic before overflow | Track counter, verify panic at u64::MAX |

### Detailed Scenario: T-EC-001 Same-Tick Events

```rust
#[test]
fn test_same_tick_determinism() {
    let clock = VirtualClock::new(TimeMode::EventDriven);
    
    // Schedule 1000 events all at t=100ns
    let mut expected_order = Vec::new();
    for i in 0..1000 {
        let id = clock.schedule(100, EventPayload::Test(i));
        expected_order.push(id);
    }
    
    // Advance to t=100
    clock.tick();
    let events = clock.tick();
    
    // Verify order matches scheduling order (by event_id)
    let actual_order: Vec<_> = events.iter().map(|e| e.event_id).collect();
    assert_eq!(expected_order, actual_order);
    
    // Repeat with fresh clock - must be identical
    let clock2 = VirtualClock::new(TimeMode::EventDriven);
    for i in 0..1000 {
        clock2.schedule(100, EventPayload::Test(i));
    }
    clock2.tick();
    let events2 = clock2.tick();
    
    let actual_order2: Vec<_> = events2.iter().map(|e| e.event_id).collect();
    assert_eq!(actual_order, actual_order2, "Same-tick ordering must be deterministic");
}
```

### Detailed Scenario: T-EC-004 Massive Time Jump

```rust
#[test]
fn test_massive_time_jump() {
    let clock = VirtualClock::new(TimeMode::EventDriven);
    
    // Schedule events across vast time range
    let e1 = clock.schedule(1, EventPayload::Test(1));                    // 1 ns
    let e2 = clock.schedule(1_000_000, EventPayload::Test(2));            // 1 ms
    let e3 = clock.schedule(1_000_000_000_000, EventPayload::Test(3));    // 1000 seconds
    
    // Single tick should jump to first event
    let batch1 = clock.tick();
    assert_eq!(batch1.len(), 1);
    assert_eq!(batch1[0].event_id, e1);
    assert_eq!(clock.now_ns(), 1);
    
    // Next tick jumps to second event
    let batch2 = clock.tick();
    assert_eq!(batch2.len(), 1);
    assert_eq!(batch2[0].event_id, e2);
    assert_eq!(clock.now_ns(), 1_000_000);
    
    // Next tick jumps 999.999 seconds
    let batch3 = clock.tick();
    assert_eq!(batch3.len(), 1);
    assert_eq!(batch3[0].event_id, e3);
    assert_eq!(clock.now_ns(), 1_000_000_000_000);
}
```

---

## 3. Memory Model Edge Cases

### Category: Concurrency Hazards

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **M-EC-001** | Classic Data Race | Two threads write same address | Both writes complete, last writer wins | Interleave two writers, verify final value |
| **M-EC-002** | Read-Write Race | Read concurrent with write | Read sees either old or new value (not torn) | 1M interleaved read/writes on u64 |
| **M-EC-003** | Torn Read (u128) | Non-atomic read of 16 bytes | May see partial update | Read u128 while writing, verify detection |
| **M-EC-004** | ABA Problem | CAS: A→B→A appears unchanged | CAS succeeds incorrectly | Log intermediate states, verify ABA detected |
| **M-EC-005** | Store Buffer Starvation | Relaxed writes never flush | Eventually visible after fence | Track visibility latency |
| **M-EC-006** | False Sharing | Two threads write adjacent addresses | Detected and reported | Write addr and addr+4, verify warning |
| **M-EC-007** | Cache Line Straddling | Write spans two cache lines | Both lines updated atomically | Write 8 bytes at line boundary |

### Category: Memory Ordering Violations

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **M-EC-010** | Missing Acquire | Read without acquire after lock | May see stale data | Verify stale read is possible |
| **M-EC-011** | Missing Release | Write without release before unlock | Other threads may not see write | Verify invisible write possible |
| **M-EC-012** | Reorder Past Acquire | Read reordered before acquire | Should be prevented | Verify ordering with logging |
| **M-EC-013** | Reorder Past Release | Write reordered after release | Should be prevented | Verify ordering with logging |
| **M-EC-014** | Acquire-Release Mismatch | Acquire load, Relaxed store | Partial synchronization | Test with flag+data pattern |

### Category: Durability & Alignment Hazards

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **M-EC-016** | Torn Writes (Power Failure) | 8-byte write interrupted mid-operation (simulated power loss) | Partial write detected, integrity check fails, recovery triggered | Inject power-cut at random byte offset, verify checksum/CRC detects corruption |
| **M-EC-017** | Unaligned Access Atomicity | Access spanning cache line boundary (e.g., 8-byte read at offset 60) | Atomicity broken, both cache lines involved, potential torn read | Read u64 at cache_line_base + 60, verify both lines locked or torn read detected |

### Detailed Scenario: M-EC-016 Torn Writes

```rust
#[test]
fn test_torn_write_detection() {
    let memory = SimulatedMemory::new(MemoryConfig {
        enable_power_failure_simulation: true,
        ..Default::default()
    });
    
    let addr = 0x3000;
    let value = 0xDEADBEEF_CAFEBABE_u64.to_le_bytes();
    
    // Initiate 8-byte write
    memory.begin_write(addr, &value, MemoryOrdering::SeqCst, 0);
    
    // Inject power failure after 4 bytes written
    memory.inject_power_failure_at_byte(4);
    
    // Attempt to finalize write (should fail)
    let result = memory.finalize_write();
    assert!(matches!(result, Err(WriteError::TornWrite { bytes_written: 4 })));
    
    // Verify integrity check detects partial write
    let integrity = memory.check_integrity(addr, 8);
    assert!(matches!(integrity, IntegrityResult::TornWrite { .. }));
}
```

### Detailed Scenario: M-EC-017 Unaligned Access

```rust
#[test]
fn test_unaligned_atomicity_violation() {
    let memory = SimulatedMemory::new(MemoryConfig::default());
    
    // Address at cache line boundary - 4 (spans two cache lines)
    let cache_line_base = 0x1000;
    let unaligned_addr = cache_line_base + 60; // 64 - 4 = spans to next line
    
    assert!(
        SimulatedMemory::cache_line_of(unaligned_addr) != 
        SimulatedMemory::cache_line_of(unaligned_addr + 7),
        "Test requires address spanning two cache lines"
    );
    
    // Concurrent writes to demonstrate non-atomicity
    let value1 = 0xAAAAAAAA_AAAAAAAA_u64;
    let value2 = 0xBBBBBBBB_BBBBBBBB_u64;
    
    // Without proper locking, interleaved writes can produce torn values
    let result = memory.simulate_concurrent_unaligned_access(
        unaligned_addr, value1, value2
    );
    
    // May see mixed bytes from both writes
    let possible_torn_values = vec![
        0xAAAAAAAA_BBBBBBBB_u64, // First 4 from value1, last 4 from value2
        0xBBBBBBBB_AAAAAAAA_u64, // Vice versa
    ];
    
    assert!(
        result == value1.to_le_bytes().to_vec() ||
        result == value2.to_le_bytes().to_vec() ||
        possible_torn_values.iter().any(|v| result == v.to_le_bytes().to_vec()),
        "Unaligned access should show potential torn read"
    );
}
```

### Detailed Scenario: M-EC-001 Classic Data Race

```rust
#[test]
fn test_data_race_detection() {
    let memory = SimulatedMemory::new(MemoryConfig::default());
    let scheduler = SchedulerOracle::new(InterleavingStrategy::Exhaustive {
        max_states: 10000,
        reduction: ReductionStrategy::Classic,
    });
    
    let addr = 0x1000;
    
    // Two tasks writing to same address
    let t1 = scheduler.spawn(100, None);
    let t2 = scheduler.spawn(100, None);
    
    // Task 1: Write 0xAAAAAAAA
    let write1 = || {
        memory.write(addr, &[0xAA; 4], MemoryOrdering::Relaxed, 0);
    };
    
    // Task 2: Write 0xBBBBBBBB
    let write2 = || {
        memory.write(addr, &[0xBB; 4], MemoryOrdering::Relaxed, 1);
    };
    
    // Run exhaustive interleaving
    let mut outcomes = HashSet::new();
    for _ in 0..1000 {
        scheduler.reset();
        
        // Interleave writes
        if scheduler.select_next() == Some(t1) {
            write1();
            write2();
        } else {
            write2();
            write1();
        }
        
        let final_value = memory.read(addr, 4, MemoryOrdering::SeqCst, 0);
        outcomes.insert(final_value);
    }
    
    // Should see both possible outcomes
    assert!(outcomes.contains(&vec![0xAA; 4]));
    assert!(outcomes.contains(&vec![0xBB; 4]));
    
    // Verify race is detected
    let races = memory.detect_data_races();
    assert!(!races.is_empty());
    assert_eq!(races[0].address, addr);
}
```

### Detailed Scenario: M-EC-004 ABA Problem

```rust
#[test]
fn test_aba_detection() {
    let memory = SimulatedMemory::new(MemoryConfig::default());
    let addr = 0x2000;
    
    // Initial value: A
    memory.write(addr, &[0xAA; 8], MemoryOrdering::SeqCst, 0);
    
    // Thread 1: Read A, get preempted
    let initial = memory.read(addr, 8, MemoryOrdering::Acquire, 0);
    assert_eq!(initial, vec![0xAA; 8]);
    
    // Thread 2: Change A → B → A
    memory.write(addr, &[0xBB; 8], MemoryOrdering::Release, 1);
    memory.write(addr, &[0xAA; 8], MemoryOrdering::Release, 1);
    
    // Thread 1: CAS expects A, sees A, succeeds (but shouldn't logically)
    let (success, _) = memory.compare_and_swap(
        addr,
        &[0xAA; 8],
        &[0xCC; 8],
        MemoryOrdering::SeqCst,
        0,
    );
    
    // CAS succeeds mechanically
    assert!(success);
    
    // But ABA should be detected
    let aba_incidents = memory.detect_aba_problems();
    assert!(!aba_incidents.is_empty());
    assert_eq!(aba_incidents[0].address, addr);
    assert_eq!(aba_incidents[0].sequence, vec![
        vec![0xAA; 8],
        vec![0xBB; 8],
        vec![0xAA; 8],
    ]);
}
```

### Detailed Scenario: M-EC-006 False Sharing

```rust
#[test]
fn test_false_sharing_detection() {
    let memory = SimulatedMemory::new(MemoryConfig::default());
    
    // Two addresses in same cache line (64 bytes)
    let addr1 = 0x1000;
    let addr2 = 0x1004;  // Only 4 bytes apart
    
    assert_eq!(
        SimulatedMemory::cache_line_of(addr1),
        SimulatedMemory::cache_line_of(addr2),
        "Test requires same cache line"
    );
    
    // Core 0 writes to addr1
    memory.write(addr1, &[0xAA; 4], MemoryOrdering::Relaxed, 0);
    
    // Core 1 writes to addr2
    memory.write(addr2, &[0xBB; 4], MemoryOrdering::Relaxed, 1);
    
    // Detect false sharing
    let incidents = memory.detect_false_sharing();
    assert_eq!(incidents.len(), 1);
    assert!(incidents[0].addresses.contains(&addr1));
    assert!(incidents[0].addresses.contains(&addr2));
}
```

---

## 4. Scheduling Edge Cases

### Category: Task Lifecycle Anomalies

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **S-EC-001** | Spawn During Tick | New task spawned while select_next() runs | Task available next tick | Spawn in callback, verify scheduling |
| **S-EC-002** | Self-Termination | Task calls terminate on itself | Clean termination, resources freed | Task calls `terminate_self()` |
| **S-EC-003** | Orphan Child Tasks | Parent terminates with running children | Children continue or are terminated (configurable) | Spawn child, kill parent, verify child state |
| **S-EC-004** | All Tasks Blocked | Every task waiting, nothing runnable | Deadlock detected OR system idle | Block all tasks, verify detection |
| **S-EC-005** | Recursive Spawn | Task spawns task that spawns task... | Stack depth limit enforced | Recursive spawn to depth 10000 |

### Category: Synchronization Hazards

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **S-EC-010** | Simple Deadlock | A waits B, B waits A | Deadlock detected | Create circular wait, verify detection |
| **S-EC-011** | Complex Deadlock | A→B→C→D→A cycle | Deadlock detected with full cycle | 4-task cycle, verify full cycle reported |
| **S-EC-012** | Priority Inversion | High-prio blocked by low-prio | Inversion detected and reported | Create inversion, verify detection |
| **S-EC-013** | Nested Lock Deadlock | Same task locks A then A again | Self-deadlock detected | Recursive lock attempt |
| **S-EC-014** | Lock Order Violation | Task 1: A→B, Task 2: B→A | Potential deadlock reported | Create lock order violation |
| **S-EC-015** | Semaphore Overclaim | Request more permits than exist | Permanent block detected | Request 10 permits from 5-permit semaphore |

### Category: Resource Contention Pathologies

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **S-EC-016** | Livelock | All tasks repeatedly yield without progress (e.g., lock contention retry loops) | Livelock detected after N consecutive yields without work | Create tasks that yield on every access, verify detection after threshold |
| **S-EC-017** | Thundering Herd | Shared resource released, thousands of blocked tasks wake simultaneously | Controlled wake-up (batch or priority-based), load spike measured | Block 10K tasks on single mutex, release, measure wake storm metrics |

### Detailed Scenario: S-EC-016 Livelock Detection

```rust
#[test]
fn test_livelock_detection() {
    let scheduler = SchedulerOracle::new(InterleavingStrategy::RoundRobin);
    let shared_resource = scheduler.create_spinlock();
    
    // Create tasks that always back off (never make progress)
    let tasks: Vec<_> = (0..4).map(|i| {
        scheduler.spawn_with_behavior(100, move |ctx| {
            loop {
                if !ctx.try_lock(shared_resource) {
                    ctx.yield_now(); // Always yields, never succeeds
                }
            }
        })
    }).collect();
    
    // Run simulation
    let result = scheduler.run_until_stable(Duration::from_secs(10));
    
    // Should detect livelock (high yield count, zero progress)
    assert!(matches!(result, SimulationResult::Livelock { 
        yield_count, 
        progress_count 
    } if yield_count > 10000 && progress_count == 0));
    
    // Verify all tasks are in yield state
    for task in &tasks {
        assert_eq!(scheduler.get_task_state(*task), TaskState::Yielding);
    }
}
```

### Detailed Scenario: S-EC-017 Thundering Herd

```rust
#[test]
fn test_thundering_herd_simulation() {
    let scheduler = SchedulerOracle::new(InterleavingStrategy::SeededRandom { seed: 42 });
    let mutex = scheduler.create_mutex();
    
    // One task holds the lock
    let holder = scheduler.spawn(100, None);
    scheduler.mutex_lock(holder, mutex);
    
    // 10,000 tasks wait for the lock
    let waiters: Vec<_> = (0..10_000).map(|i| {
        let task = scheduler.spawn(50 + (i % 100) as u8, None);
        scheduler.mutex_lock_async(task, mutex);
        task
    }).collect();
    
    // Release the lock - thundering herd!
    let metrics = scheduler.release_with_metrics(holder, mutex);
    
    // Verify herd behavior
    assert!(metrics.simultaneous_wakeups > 1000, 
        "Expected thundering herd, got {} wakeups", metrics.simultaneous_wakeups);
    
    // Verify controlled mitigation if enabled
    if scheduler.config().thundering_herd_mitigation {
        assert!(metrics.wake_batches > 1, "Should batch wakeups");
        assert!(metrics.max_batch_size <= 100, "Batches should be limited");
    }
    
    // Record for analysis
    scheduler.record_herd_event(ThunderingHerdEvent {
        mutex_id: mutex,
        waiter_count: waiters.len(),
        wake_pattern: metrics.wake_pattern.clone(),
        total_wake_time_ns: metrics.total_time_ns,
    });
}
```

### Detailed Scenario: S-EC-010 Simple Deadlock

```rust
#[test]
fn test_simple_deadlock_detection() {
    let scheduler = SchedulerOracle::new(InterleavingStrategy::RoundRobin);
    
    let mutex_a = scheduler.create_mutex();
    let mutex_b = scheduler.create_mutex();
    
    let task_1 = scheduler.spawn(100, None);
    let task_2 = scheduler.spawn(100, None);
    
    // Task 1: Lock A, try to lock B
    scheduler.mutex_lock(task_1, mutex_a);
    
    // Task 2: Lock B, try to lock A
    scheduler.mutex_lock(task_2, mutex_b);
    
    // Task 1: Try to lock B (blocks)
    scheduler.mutex_lock_async(task_1, mutex_b);
    
    // Task 2: Try to lock A (blocks - deadlock!)
    scheduler.mutex_lock_async(task_2, mutex_a);
    
    // Verify deadlock is detected
    let deadlock = scheduler.detect_deadlock();
    assert!(deadlock.is_some());
    
    let cycle = deadlock.unwrap().cycle;
    assert!(cycle.contains(&task_1));
    assert!(cycle.contains(&task_2));
}
```

### Detailed Scenario: S-EC-012 Priority Inversion

```rust
#[test]
fn test_priority_inversion_detection() {
    let scheduler = SchedulerOracle::new(InterleavingStrategy::RoundRobin);
    
    let mutex = scheduler.create_mutex();
    
    // Low priority task
    let low = scheduler.spawn(10, None);  // Priority 10 (low)
    
    // High priority task
    let high = scheduler.spawn(200, None);  // Priority 200 (high)
    
    // Low takes the lock
    scheduler.mutex_lock(low, mutex);
    
    // High tries to take lock (blocks on low)
    scheduler.mutex_lock_async(high, mutex);
    
    // Detect priority inversion
    let inversions = scheduler.detect_priority_inversions();
    assert_eq!(inversions.len(), 1);
    
    let inv = &inversions[0];
    assert_eq!(inv.high_priority_task, high);
    assert_eq!(inv.low_priority_holder, low);
    assert_eq!(inv.high_priority, 200);
    assert_eq!(inv.low_priority, 10);
}
```

---

## 5. Hardware Fault Injection

### Category: Probabilistic Failures

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **H-EC-001** | Single Bit Flip | Random bit flip in memory | Detected by checksums, reported | Inject flip, verify detection |
| **H-EC-002** | Multi-Bit Corruption | Multiple bits corrupted | Detected, data marked invalid | Inject multi-bit error |
| **H-EC-003** | Silent Data Corruption | Undetected memory error | Should be caught by redundancy | Compare with shadow copy |
| **H-EC-004** | Interrupt Delay | IRQ delayed by N cycles | System remains consistent | Delay timer interrupt |
| **H-EC-005** | Spurious Interrupt | Unexpected interrupt fires | Handled gracefully | Inject random interrupt |
| **H-EC-006** | Clock Drift | Hardware clock runs fast/slow | Virtual time unaffected | Simulate drift in RealTime mode |

### Category: Resource Exhaustion

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **H-EC-010** | Memory Exhaustion | Allocation fails | OOM error, graceful degradation | Allocate until failure |
| **H-EC-011** | Event Queue Overflow | Too many pending events | Backpressure or rejection | Schedule 10M events |
| **H-EC-012** | Task Table Full | Maximum tasks reached | Clear error, no crash | Spawn until limit |
| **H-EC-013** | File Descriptor Exhaustion | All FDs in use | Error returned, no leak | Open until failure |

### Detailed Scenario: H-EC-001 Single Bit Flip

```rust
#[test]
fn test_bit_flip_detection() {
    let memory = SimulatedMemory::new(MemoryConfig {
        enable_ecc: true,
        enable_checksums: true,
        ..Default::default()
    });
    
    let addr = 0x5000;
    let original_data = vec![0x12, 0x34, 0x56, 0x78];
    
    // Write original data
    memory.write(addr, &original_data, MemoryOrdering::SeqCst, 0);
    
    // Inject single bit flip
    memory.inject_bit_flip(addr, 0);  // Flip bit 0 of first byte
    
    // Read should detect corruption
    let result = memory.read_with_integrity_check(addr, 4, MemoryOrdering::SeqCst, 0);
    
    match result {
        IntegrityResult::Valid(_) => panic!("Should have detected bit flip"),
        IntegrityResult::Corrected(data, error) => {
            assert_eq!(data, original_data);
            assert!(matches!(error, IntegrityError::SingleBitFlip { .. }));
        }
        IntegrityResult::Corrupted(error) => {
            assert!(matches!(error, IntegrityError::MultibitError { .. }));
        }
    }
}
```

### Detailed Scenario: H-EC-004 Interrupt Delay

```rust
#[test]
fn test_interrupt_delay_resilience() {
    let clock = VirtualClock::new(TimeMode::FixedTick { interval_ns: 1000 });
    let scheduler = SchedulerOracle::new(InterleavingStrategy::RoundRobin);
    
    // Schedule timer interrupt every 10000 ns
    let timer_interval = 10000;
    clock.schedule(timer_interval, EventPayload::TimerInterrupt);
    
    // Simulate interrupt handling delay
    let interrupt_latency = 500; // 500 ns delay
    
    // Run simulation
    for _ in 0..100 {
        let events = clock.tick();
        
        for event in events {
            if matches!(event.payload, EventPayload::TimerInterrupt) {
                // Simulate delayed handling
                let handle_time = event.scheduled_at_ns + interrupt_latency;
                
                // System should remain consistent
                assert!(
                    scheduler.check_consistency(),
                    "System inconsistent after delayed interrupt"
                );
                
                // Reschedule next interrupt
                clock.schedule(timer_interval, EventPayload::TimerInterrupt);
            }
        }
    }
}
```

---

## 6. Kernel-Specific Edge Cases

### Category: Tenant Isolation Violations (Must Never Occur)

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **K-EC-001** | Cross-Tenant Read | Tenant A reads Tenant B's memory | Access denied, error returned | Attempt cross-tenant read |
| **K-EC-002** | Cross-Tenant Write | Tenant A writes Tenant B's memory | Access denied, error returned | Attempt cross-tenant write |
| **K-EC-003** | Path Traversal | Tenant accesses `/../other_tenant/` | Path remapped, access denied | Try `..` path escapes |
| **K-EC-004** | Shared Resource Leak | Info leaks through shared state | No shared mutable state | Audit all globals |

### Category: Resource Quota Violations

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **K-EC-010** | Heap Limit Exceeded | Tenant allocates beyond quota | Allocation fails, OOM error | Allocate to limit+1 |
| **K-EC-011** | Heap Limit After GC | Over limit, but GC can free | GC triggered, allocation retried | Fill heap, release refs, allocate |
| **K-EC-012** | CPU Time Exceeded | Execution runs too long | Watchdog terminates | Infinite loop, verify termination |
| **K-EC-013** | Concurrent Request Flood | Exceed max_concurrent | Requests queued or rejected | Send burst of requests |
| **K-EC-014** | Graceful Degradation | System under load | Lower tiers throttled first | Load test with mixed tiers |

### Category: Security & Side-Channel Attacks

| ID | Scenario | Description | Expected Behavior | Test Strategy |
|----|----------|-------------|-------------------|---------------|
| **K-EC-015** | Side-Channel Simulation (Cache Timing) | Tenant A infers Tenant B's data via cache access timing patterns | Timing variations detected and reported; optional cache partitioning enabled | Measure cache hit/miss timing variance across tenants, verify detection threshold |
| **K-EC-016** | GC Resource Attack | Malicious tenant triggers excessive GC to steal CPU time from co-located tenants | GC time charged to triggering tenant; cross-tenant impact limited | Allocate/free rapidly, measure GC impact on other tenants' latency |

### Detailed Scenario: K-EC-015 Side-Channel Detection

```rust
#[test]
fn test_cache_side_channel_detection() {
    let pool = SovereignPool::new(default_journal(), PoolConfig {
        enable_side_channel_detection: true,
        cache_partitioning: CachePartitioning::Strict,
        ..Default::default()
    });
    
    pool.register_tenant("victim", TenantTier::Enterprise);
    pool.register_tenant("attacker", TenantTier::Standard);
    
    // Victim accesses secret data (creates cache footprint)
    pool.execute_isolated("victim", |runtime| {
        runtime.execute_script("secret_access", r#"
            const secret = new Uint8Array(4096);
            for (let i = 0; i < 1000; i++) {
                secret[i * 4] = i; // Access pattern leaves cache trace
            }
        "#.to_string())
    }).unwrap();
    
    // Attacker attempts to probe cache timing
    let probe_result = pool.execute_isolated("attacker", |runtime| {
        runtime.execute_script("probe", r#"
            const probe = new Uint8Array(4096);
            const timings = [];
            
            for (let i = 0; i < 1000; i++) {
                const start = performance.now();
                const _ = probe[i * 4];
                const end = performance.now();
                timings.push(end - start);
            }
            
            // Try to detect cache hits/misses
            JSON.stringify(timings);
        "#.to_string())
    });
    
    // Side-channel attempt should be detected
    let security_events = pool.get_security_events("attacker");
    assert!(security_events.iter().any(|e| 
        matches!(e, SecurityEvent::SideChannelAttempt { 
            attack_type: SideChannelType::CacheTiming, 
            .. 
        })
    ));
    
    // With strict partitioning, timings should be uniform (no information leak)
    if let Ok(timings_json) = probe_result {
        let timings: Vec<f64> = serde_json::from_str(&timings_json).unwrap();
        let variance = statistical_variance(&timings);
        assert!(variance < 0.001, "Timing variance too high, potential leak");
    }
}
```

### Detailed Scenario: K-EC-016 GC Resource Attack

```rust
#[test]
fn test_gc_resource_attack_mitigation() {
    let pool = SovereignPool::new(default_journal(), PoolConfig {
        gc_time_accounting: GcTimeAccounting::PerTenant,
        max_gc_time_ratio: 0.1, // Max 10% of CPU on GC
        ..Default::default()
    });
    
    pool.register_tenant("attacker", TenantTier::Free);
    pool.register_tenant("victim", TenantTier::Enterprise);
    
    // Start victim's long-running computation
    let victim_handle = pool.execute_isolated_async("victim", |runtime| {
        runtime.execute_script("computation", r#"
            let result = 0;
            for (let i = 0; i < 10_000_000; i++) {
                result += Math.sqrt(i);
            }
            result;
        "#.to_string())
    });
    
    // Attacker tries to trigger excessive GC
    let attacker_result = pool.execute_isolated("attacker", |runtime| {
        runtime.execute_script("gc_attack", r#"
            // Rapidly allocate and discard to trigger GC storms
            for (let round = 0; round < 1000; round++) {
                const garbage = [];
                for (let i = 0; i < 10000; i++) {
                    garbage.push({ data: new Array(1000).fill(round) });
                }
                // Discard all - triggers GC
            }
            "attack_complete";
        "#.to_string())
    });
    
    // Wait for victim
    let victim_result = victim_handle.await_result();
    
    // Verify GC time was charged to attacker
    let attacker_metrics = pool.get_tenant_metrics("attacker");
    let victim_metrics = pool.get_tenant_metrics("victim");
    
    // Attacker should have high GC time
    assert!(attacker_metrics.gc_time_ns > victim_metrics.gc_time_ns * 10,
        "GC time should be attributed to attacker");
    
    // Victim's computation should not be severely impacted
    assert!(victim_metrics.execution_time_ns < victim_metrics.expected_time_ns * 1.2,
        "Victim should not be delayed more than 20%");
    
    // Attacker may be throttled or terminated
    assert!(
        attacker_result.is_err() || 
        attacker_metrics.throttle_events > 0,
        "Attacker should be throttled"
    );
}
```

### Detailed Scenario: K-EC-001 Cross-Tenant Read Attempt

```rust
#[test]
fn test_cross_tenant_isolation() {
    let pool = SovereignPool::new(default_journal(), default_config());
    
    // Create two tenants
    pool.register_tenant("tenant-a", TenantTier::Standard);
    pool.register_tenant("tenant-b", TenantTier::Standard);
    
    // Tenant A stores a secret
    let secret = vec![0xDE, 0xAD, 0xBE, 0xEF];
    pool.execute_isolated("tenant-a", |runtime| {
        runtime.execute_script("store", r#"
            globalThis.secret = new Uint8Array([0xDE, 0xAD, 0xBE, 0xEF]);
        "#.to_string())
    }).unwrap();
    
    // Tenant B attempts to read Tenant A's secret
    let result = pool.execute_isolated("tenant-b", |runtime| {
        runtime.execute_script("steal", r#"
            // These should all fail or return undefined
            const attempts = [
                () => globalThis.secret,
                () => Deno.core.ops.op_read_tenant_memory("tenant-a", 0x1000),
                () => eval('globalThis.secret'),
            ];
            
            for (const attempt of attempts) {
                try {
                    const value = attempt();
                    if (value !== undefined) {
                        throw new Error("Isolation violation: " + value);
                    }
                } catch (e) {
                    // Expected - access denied
                }
            }
            
            "isolation_intact"
        "#.to_string())
    });
    
    // Tenant B should not have access
    match result {
        Ok(value) => assert_eq!(value, "isolation_intact"),
        Err(e) => panic!("Unexpected error: {}", e),
    }
}
```

### Detailed Scenario: K-EC-012 CPU Time Exceeded

```rust
#[test]
fn test_watchdog_termination() {
    let pool = SovereignPool::new(default_journal(), PoolConfig {
        default_tier: TenantTier::Free,  // 100ms max execution
        ..Default::default()
    });
    
    pool.register_tenant("infinite-loop", TenantTier::Free);
    
    let start = Instant::now();
    
    let result = pool.execute_isolated("infinite-loop", |runtime| {
        runtime.execute_script("loop", r#"
            // Infinite loop
            while (true) {
                // Burn CPU
                let x = 0;
                for (let i = 0; i < 1000000; i++) {
                    x += i;
                }
            }
        "#.to_string())
    });
    
    let elapsed = start.elapsed();
    
    // Should have been terminated
    assert!(matches!(result, Err(TenantError::ExecutionTimeout { .. })));
    
    // Should not have run much longer than the limit
    let max_expected = Duration::from_millis(150);  // 100ms + buffer
    assert!(
        elapsed < max_expected,
        "Execution took {:?}, expected < {:?}",
        elapsed,
        max_expected
    );
}
```

---

## 7. Edge Case Test Matrix Summary

### Coverage Requirements

| Category | Total Cases | Critical | High | Medium | Low |
|----------|-------------|----------|------|--------|-----|
| Temporal | 7 | 3 | 2 | 2 | 0 |
| Memory | 16 | 6 | 6 | 3 | 1 |
| Scheduling | 12 | 5 | 5 | 2 | 0 |
| Hardware | 9 | 2 | 3 | 3 | 1 |
| Kernel | 10 | 6 | 3 | 1 | 0 |
| **Total** | **54** | **22** | **19** | **11** | **2** |

*Updated: Added M-EC-016/017 (Torn Writes, Unaligned Access), S-EC-016/017 (Livelock, Thundering Herd), K-EC-015/016 (Side-Channel, GC Attack)*

### Cross-Reference to TLA+ Invariants

| Edge Case | TLA+ Invariant | Verification Level |
|-----------|----------------|-------------------|
| K-EC-015 | `SideChannelFreedom` | V-Level 4+ |
| K-EC-016 | `FairResourceAccounting` | V-Level 3+ |
| S-EC-016 | `NoLivelock` | V-Level 3+ |
| S-EC-017 | `BoundedWakeup` | V-Level 2+ |
| M-EC-016 | `WriteAtomicity` | V-Level 4+ |
| M-EC-017 | `AlignmentSafety` | V-Level 3+ |

### Priority Definitions

| Priority | Definition | Required Coverage |
|----------|------------|-------------------|
| **Critical** | Security or data integrity | 100% automated, Kani proof |
| **High** | Correctness, determinism | 100% automated |
| **Medium** | Performance, edge behavior | 90% automated |
| **Low** | Rare conditions | 80% automated |

### Automated Test Distribution

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     TEST PYRAMID FOR EDGE CASES                         │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│                           ╱╲                                            │
│                          ╱  ╲   TLA+ Model Checking                     │
│                         ╱    ╲  (All Critical Cases)                    │
│                        ╱──────╲                                         │
│                       ╱        ╲                                        │
│                      ╱   Kani   ╲  Formal Proofs                        │
│                     ╱   Proofs   ╲ (Critical + High)                    │
│                    ╱──────────────╲                                     │
│                   ╱                ╲                                    │
│                  ╱   Integration    ╲  Simulation Tests                 │
│                 ╱   Simulation       ╲ (All Categories)                 │
│                ╱──────────────────────╲                                 │
│               ╱                        ╲                                │
│              ╱      Unit Tests          ╲  Fast, Isolated               │
│             ╱      (All Cases)           ╲                              │
│            ╱──────────────────────────────╲                             │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## 8. Regression Test Requirements

Every bug fix must:

1. Add a new edge case entry to this document
2. Add automated test that reproduces the bug
3. Verify fix passes Kani (if applicable)
4. Update TLA+ model (if invariant was violated)

### Template for New Edge Cases

```markdown
| **ID** | [CATEGORY]-EC-XXX |
|--------|-------------------|
| **Scenario** | Brief description |
| **Description** | Detailed explanation |
| **Root Cause** | Why this can happen |
| **Expected Behavior** | What should happen |
| **Test Strategy** | How to verify |
| **TLA+ Coverage** | Which invariant |
| **Kani Proof** | Proof function name |
| **Added** | YYYY-MM-DD |
| **Author** | Name |
```

---

*"Every edge case not tested is a bug waiting to happen."*

— K-ACA v2.0