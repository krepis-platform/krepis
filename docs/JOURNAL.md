# Sovereign Journal System

## Overview

The Krepis Kernel implements a **persistent transaction journal** using Sled DB, providing:

- **Atomic operations**: All state changes are durably persisted
- **Crash recovery**: Stats and operations survive kernel restarts
- **Audit trail**: Complete history of all operations
- **Zero data loss**: ACID guarantees at the storage layer

## Architecture

```
┌─────────────────────────────────────┐
│   Deno Runtime (JS Execution)       │
└────────────┬────────────────────────┘
             │ op_increment_stats()
             ↓
┌─────────────────────────────────────┐
│   Rust Ops Layer                    │
│   ├─ In-memory update               │
│   └─ Journal write (atomic)         │
└────────────┬────────────────────────┘
             ↓
┌─────────────────────────────────────┐
│   Sled DB (./.krepis/storage)       │
│   ├─ journal tree (operations)      │
│   └─ stats tree (counters)          │
└─────────────────────────────────────┘
```

## Data Model

### TransactionLog

```rust
pub struct TransactionLog {
    pub timestamp: i64,      // Unix timestamp in milliseconds
    pub op_name: String,     // Operation identifier
    pub request_id: String,  // Request correlation ID
    pub status: LogStatus,   // Started/Completed/Failed
}
```

### Storage Trees

1. **journal** tree: Stores all transaction logs
   - Key: `{timestamp}:{request_id}`
   - Value: JSON-serialized `TransactionLog`

2. **stats** tree: Stores operation counters
   - Key: `op_count:{op_name}`
   - Value: u64 (little-endian bytes)

## Operations

### Logging Transactions

```rust
journal.log_transaction(&TransactionLog {
    timestamp: now(),
    op_name: "kernel_init".to_string(),
    request_id: ctx.request_id.clone(),
    status: LogStatus::Started,
})?;
```

### Incrementing Counters

```rust
let new_count = journal.increment_op_count("js_ops_called")?;
```

This operation is **atomic** and **durable**:
1. Read current value
2. Increment
3. Write back
4. Flush to disk

### Recovery

On kernel startup:

```rust
let recovered_ops = journal.recover_op_count("js_ops_called")?;
let stats = SovereignStats {
    js_ops_called: recovered_ops,
    // ...
};
```

## Persistence Guarantees

- **Durability**: All operations call `flush()` to ensure disk sync
- **Atomicity**: Uses Sled's transactional `update_and_fetch`
- **Consistency**: Single-writer model prevents conflicts
- **Isolation**: Each counter operates independently

## Performance Characteristics

- **Write latency**: ~1-5ms (includes fsync)
- **Read latency**: ~100-500μs (from page cache)
- **Crash recovery**: O(1) - reads latest counter values
- **Space overhead**: ~100 bytes per log entry

## Testing

### Unit Tests

```bash
cargo test --package krepis-kernel --lib journal
```

### Integration Tests

```bash
cargo test --package krepis-kernel --test sovereign_test test_journal_persistence
cargo test --package krepis-kernel --test sovereign_test test_kernel_restart_recovery
```

### Manual Testing

```bash
# First run
cargo run --package krepis-kernel
# Note the op count

# Second run (recovery test)
cargo run --package krepis-kernel
# Verify count increases from previous value
```

## Storage Location

Default: `./.krepis/storage`

```
.krepis/
└── storage/
    ├── conf          # Sled metadata
    ├── db            # Main database file
    └── blobs/        # Large value storage
```

## API Reference

### SovereignJournal

```rust
pub struct SovereignJournal {
    // ...
}

impl SovereignJournal {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self>;
    pub fn log_transaction(&self, log: &TransactionLog) -> Result<()>;
    pub fn increment_op_count(&self, op_name: &str) -> Result<u64>;
    pub fn recover_op_count(&self, op_name: &str) -> Result<u64>;
    pub fn journal_count(&self) -> usize;
    pub fn clear_all(&self) -> Result<()>;
    pub fn get_recent_logs(&self, limit: usize) -> Result<Vec<TransactionLog>>;
}
```

## Design Decisions

### Why Sled?

- Embedded (no external dependencies)
- ACID guarantees
- Lock-free concurrent reads
- Zero-copy architecture
- Rust-native API

### Why Not SQLite?

- Sled is faster for key-value workloads
- Better concurrency model
- Native Rust integration
- No SQL overhead

### Why Flush Every Write?

**Durability over throughput**: In a sovereign kernel, correctness is paramount. Every state change must survive crashes.

Future optimization: Batch flushes with a configurable interval.

## Future Enhancements

- [ ] Configurable flush policy (sync/async)
- [ ] Compression for journal entries
- [ ] Automatic log rotation
- [ ] Distributed journal (multi-node)
- [ ] Metrics export (Prometheus)