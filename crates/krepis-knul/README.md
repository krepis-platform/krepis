# Krepis KNUL - Network Adapter Layer

QUIC server lifecycle management for the Krepis platform.

Implements the FFI bridge between Deno TypeScript (KNUL Adapter) and Rust kernel components.

## Architecture

```
┌──────────────────────────────┐
│   Deno TypeScript Layer      │
│   (KNUL Adapter)             │
└────────────┬─────────────────┘
             │ FFI Boundary
             │ (extern "C" functions)
             ▼
┌──────────────────────────────┐
│   Krepis KNUL (Rust)         │
│  ┌──────────────────────────┐│
│  │   FFI Entry Points       ││
│  │  (krepis_quic_start etc) ││
│  └──────────┬───────────────┘│
│             │                │
│  ┌──────────▼───────────────┐│
│  │  Server Registry         ││
│  │  (DashMap<u64, Server>)  ││
│  └──────────┬───────────────┘│
│             │                │
│  ┌──────────▼───────────────┐│
│  │  QuicServer Instance     ││
│  │  (Lifecycle + Stats)     ││
│  └──────────────────────────┘│
└──────────────────────────────┘
```

## Module Structure

### src/lib.rs - FFI Entry Points

Exposes three extern "C" functions for server lifecycle management:

```rust
#[no_mangle]
pub extern "C" fn krepis_quic_start(config_ptr: *const FfiQuicConfig) -> FfiResponse
pub extern "C" fn krepis_quic_stop(server_handle: u64) -> FfiResponse
pub extern "C" fn krepis_quic_get_stats(server_handle: u64) -> FfiResponse
```

**Global State:**
- `SERVER_REGISTRY`: Static, thread-safe registry for all active servers

**Implementation Notes:**
- Functions are synchronous from Rust perspective
- Actual async work happens in spawned tokio tasks
- Results are returned via `FfiResponse` (from krepis-core)

### src/server.rs - Server Instance

`QuicServer` struct manages a single QUIC server:

```rust
pub struct QuicServer {
    pub handle: u64,
    pub config: FfiQuicConfig,
    running: AtomicBool,
    startup_time_ms: u64,
    stats_total_requests: Arc<AtomicU64>,
    // ... more stats ...
}
```

**Key Methods:**
- `new()`: Create new instance (not yet started)
- `async start()`: Initialize quinn endpoint, bind port, accept connections
- `async stop()`: Graceful shutdown, wait for active connections
- `get_stats()`: Snapshot current metrics
- `is_running()`: Check running state

**Statistics Tracking:**
- Total requests processed
- Bytes in/out
- Active connections
- Error count
- Uptime
- Average latency (to be implemented)

### src/registry.rs - Instance Registry

`ServerRegistry` provides thread-safe concurrent access:

```rust
pub struct ServerRegistry {
    servers: DashMap<u64, Arc<QuicServer>>,
    allocator: HandleAllocator,
}
```

**Key Methods:**
- `register(server)`: Add server, get unique handle
- `get(handle)`: Lookup server by handle (returns Arc)
- `unregister(handle)`: Remove server from registry
- `list_handles()`: List all active handles
- `count()`: Number of registered servers
- `iter()`: Iterate all servers

**Design:**
- Uses DashMap for lock-free concurrent access
- Handles are globally unique u64 values
- Arc allows safe sharing across threads/async tasks
- Thread-safe: no mutexes, no global locks needed

## FFI Contract

### Function Signatures

All functions follow the Sovereign Bridge ABI v1.1.0:

```c
FfiResponse krepis_quic_start(const FfiQuicConfig* config_ptr);
FfiResponse krepis_quic_stop(uint64_t server_handle);
FfiResponse krepis_quic_get_stats(uint64_t server_handle);
```

### Error Handling

Functions return `FfiResponse`:

```rust
pub struct FfiResponse {
    pub error_code: u32,      // 0 = success
    pub _reserved: u32,
    pub result_buffer: FfiBuffer,
}
```

Error codes from `KrepisError`:
- `0`: Success
- `1000`: Internal error
- `1004`: Invalid pointer/handle
- `4001`: Invalid request (bad config)
- `5000`: Network error (port in use)
- `2000`: Timeout

## Usage Example

### From Deno TypeScript

```typescript
import { loadKrepisCore } from "@krepis/core";
import { AdapterBuilder, AdapterProtocol } from "@krepis/knul";

// Build adapter configuration
const adapter = new AdapterBuilder()
  .protocol(AdapterProtocol.QUIC)
  .host("127.0.0.1")
  .port(4433)
  .certPath("./certs/cert.pem")
  .keyPath("./certs/key.pem")
  .build();

// FFI calls happen internally via kernel library
await adapter.start();

// Get statistics
const stats = adapter.getStats();
console.log(`Active connections: ${stats.activeConnections}`);

await adapter.stop();
```

### From Rust (Internal)

```rust
use krepis_knul::{get_registry, QuicServer};
use krepis_core::FfiQuicConfig;

let registry = get_registry();

// Create server
let config = FfiQuicConfig { /* ... */ };
let mut server = QuicServer::new(0, config);

// Register and get handle
let handle = registry.register(server);

// Start server
// let result = server.start().await;

// Later: stop server
// registry.unregister(handle);
```

## Thread Safety

### DashMap-based Registry

- No global mutexes
- Lock-free concurrent reads
- Fine-grained per-bucket locking on writes
- Safe for concurrent access from multiple threads

### Arc<QuicServer> Sharing

- Multiple threads can hold references to same server
- Server state updated atomically (AtomicU64, AtomicBool)
- Safe to share across async task boundaries

### Tokio Runtime

- Server lifecycle tasks run on tokio thread pool
- FFI entry points may be called from Deno thread pool
- No cross-thread synchronization issues due to Arc/DashMap

## Error Handling

### Invalid Handles

```rust
if let Some(server) = registry.get(handle) {
    // Use server...
} else {
    // Return InvalidPointer error
    return FfiResponse::error(KrepisError::InvalidPointer as u32);
}
```

### Port Conflicts

```rust
match server.start().await {
    Ok(()) => FfiResponse::success(...),
    Err(msg) if msg.contains("bind") => {
        FfiResponse::error(KrepisError::NetworkError as u32)
    }
    Err(_) => FfiResponse::error(KrepisError::Internal as u32),
}
```

## Performance Characteristics

### Handle Allocation

- O(1) time: Atomic increment
- No allocation overhead

### Server Lookup

- O(1) expected time: DashMap hash table
- Lock-free reads (in typical case)

### Statistics Collection

- O(1) time: Snapshot atomic counters
- No blocking, concurrent-safe

### Shutdown

- O(n) where n = active connections
- Graceful drain with timeout
- Force close on timeout

## Testing

```bash
# Run all tests
cargo test

# Run with logging
RUST_LOG=debug cargo test -- --nocapture

# Benchmark
cargo bench
```

### Test Coverage

- Registry: unique handles, concurrent access, lookup, removal
- Server: creation, statistics, concurrent recordings
- Statistics: JSON serialization, uptime calculation

## Dependencies

| Crate | Version | Purpose |
|-------|---------|---------|
| `krepis-core` | 0.1.0 | FFI structures, error codes |
| `tokio` | 1.42 | Async runtime |
| `quinn` | 0.11 | QUIC protocol |
| `dashmap` | 5.5 | Concurrent map |
| `serde_json` | 1.0 | Stats serialization |
| `rustls` | 0.22 | TLS crypto |

## Future Work

- [ ] Connection pooling
- [ ] Per-connection latency tracking
- [ ] Graceful flow control
- [ ] Connection migration support
- [ ] QUIC extension support
- [ ] Memory pool optimization
- [ ] Metrics export (Prometheus)

## Principle: Sovereign Link

This crate implements only the **communication layer**:
- ✅ Network I/O
- ✅ Server lifecycle
- ✅ Statistics collection
- ✅ Configuration management

It does **NOT** handle:
- ❌ Business logic
- ❌ Request processing
- ❌ Authentication/authorization
- ❌ Data persistence

Business logic resides in the Kernel (Rust) or user applications (TypeScript).

## References

- **Core ABI**: [crates/krepis-core/src/abi.rs](../krepis-core/src/abi.rs)
- **QUIC Spec**: [docs/QUIC_FFI_SPEC.md](../../docs/QUIC_FFI_SPEC.md)
- **KNUL Adapter**: [packages/deno-krepis-knul/adapter.ts](../../packages/deno-krepis-knul/adapter.ts)

## License

Apache 2.0 (matching Krepis project)