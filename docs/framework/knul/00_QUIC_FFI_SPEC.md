# Krepis QUIC Server FFI Specification

## Overview

This document specifies the FFI contract for QUIC server lifecycle management between Krepis KNUL (adapter layer) and Krepis Core (Rust kernel).

**ABI Version:** 1.1.0  
**Alignment:** 8-byte aligned (64-bit systems)  
**Protocol:** QUIC (UDP-based, RFC 9000)

## Architecture

```
┌─────────────────────────────┐
│   Deno TypeScript Layer     │
│   (KNUL Adapter)            │
└────────┬────────────────────┘
         │ FFI Boundary
         │ (extern "C" functions)
         ▼
┌─────────────────────────────┐
│   Krepis Core (Rust)        │
│   (Kernel + QUIC Server)    │
└─────────────────────────────┘
```

## Type Definitions

### FfiQuicConfig

Configuration structure for QUIC server initialization.

**Memory Layout (112 bytes, 8-byte aligned):**

```
Offset  Type            Field           Bytes   Description
──────────────────────────────────────────────────────────
0x00    u16             port            2       UDP listen port
0x02    u16             _padding1       2       Alignment padding
0x04    u32             max_streams     4       Max concurrent streams
0x08    u64             idle_timeout_ms 8       Connection idle timeout (ms)
0x10    FfiBuffer       host_addr       32      Bind address (e.g., "127.0.0.1")
0x30    FfiBuffer       cert_path       32      Path to TLS certificate (PEM)
0x50    FfiBuffer       key_path        32      Path to TLS private key (PEM)
```

**Total: 112 bytes**

**Field Descriptions:**

- **port** (u16): UDP port number (1-65535)
  - 0 is invalid
  - Common QUIC port: 443

- **max_streams** (u32): Maximum number of concurrent streams per connection
  - Minimum: 1
  - Typical: 1000

- **idle_timeout_ms** (u64): How long to keep idle connections alive
  - Minimum: 1000 (1 second)
  - Typical: 120000 (2 minutes)

- **host_addr** (FfiBuffer): Host address to bind to
  - Null-terminated string
  - Examples: "127.0.0.1", "0.0.0.0", "::1" (IPv6)
  - Must be valid and not exceed max_payload_bytes

- **cert_path** (FfiBuffer): Path to TLS certificate file
  - Null-terminated string
  - Format: PEM-encoded certificate chain
  - Example: "/etc/ssl/certs/server.crt"

- **key_path** (FfiBuffer): Path to TLS private key file
  - Null-terminated string
  - Format: PEM-encoded private key
  - Example: "/etc/ssl/private/server.key"

### FfiResponse

Standard response structure for all QUIC FFI functions.

**Memory Layout (40 bytes, 8-byte aligned):**

```
Offset  Type        Field           Bytes   Description
──────────────────────────────────────────────────
0x00    u32         error_code      4       Error code (0 = success)
0x04    u32         _reserved       4       Reserved
0x08    FfiBuffer   result_buffer   32      Response payload
```

## FFI Functions

### krepis_quic_start

Start a new QUIC server instance.

**Signature:**
```c
FfiResponse krepis_quic_start(const FfiQuicConfig* config_ptr);
```

**Parameters:**
- `config_ptr` (const FfiQuicConfig*): Pointer to valid, properly aligned FfiQuicConfig

**Returns:** FfiResponse
- `error_code`: 0 on success, KrepisError code on failure
- `result_buffer.data`: Points to u64 server handle (if successful)
- `result_buffer.len`: 8 (size of u64)
- `result_buffer.cap`: 8

**Success Response:**
```
error_code: 0
result_buffer:
  data: <pointer to u64 server_handle in kernel memory>
  len: 8
  cap: 8
```

**Error Response:**
```
error_code: KrepisError code
result_buffer:
  data: null
  len: 0
  cap: 0
```

**Possible Errors:**
- `KrepisError::InvalidRequest` (4001): Configuration is invalid
  - port is 0 or out of range
  - max_streams is 0
  - Buffer paths are invalid
- `KrepisError::NetworkError` (5000): Failed to bind to port
  - Port already in use
  - Invalid host address
- `KrepisError::Internal` (1000): Server initialization failed
  - TLS certificate loading failed
  - QUIC context setup failed

**Side Effects:**
- Loads TLS certificates from file system
- Creates QUIC socket
- Binds to specified port
- Begins accepting connections
- Allocates server handle (u64)

**Thread Safety:**
- Function is thread-safe
- Multiple servers can be started simultaneously
- Each server has unique handle

**Memory Management:**
- Input config and buffers managed by caller
- Output server handle managed by kernel
- Handle must be freed with krepis_quic_stop()

**Example Usage (TypeScript via Deno FFI):**
```typescript
const config: FfiQuicConfig = {
  port: 4433,
  _padding1: 0,
  max_streams: 1000,
  idle_timeout_ms: 120000,
  host_addr: FfiBuffer with "127.0.0.1",
  cert_path: FfiBuffer with "/path/to/cert.pem",
  key_path: FfiBuffer with "/path/to/key.pem",
};

const response = await kernelFFI.symbols.krepis_quic_start(
  Deno.UnsafePointer.of(config)
);

if (response.error_code === 0) {
  const handlePtr = response.result_buffer.data;
  const serverHandle = readU64(handlePtr);
  // Use serverHandle with krepis_quic_stop()
}
```

---

### krepis_quic_stop

Gracefully shut down a running QUIC server.

**Signature:**
```c
FfiResponse krepis_quic_stop(uint64_t server_handle);
```

**Parameters:**
- `server_handle` (u64): Handle returned by krepis_quic_start()

**Returns:** FfiResponse
- `error_code`: 0 on success, KrepisError code on failure
- `result_buffer`: Empty (not used)

**Success Response:**
```
error_code: 0
result_buffer:
  data: null
  len: 0
  cap: 0
```

**Error Response:**
```
error_code: KrepisError code
result_buffer: (empty)
```

**Possible Errors:**
- `KrepisError::InvalidPointer` (1004): Handle is invalid or stale
- `KrepisError::Timeout` (2000): Graceful shutdown exceeded timeout
  - In-flight requests didn't complete within timeout
  - Force close will be attempted
- `KrepisError::Internal` (1000): Shutdown failed

**Side Effects:**
- Signals all active connections to drain
- Closes QUIC socket
- Releases TLS context
- Frees server handle
- Handle becomes invalid after call

**Shutdown Sequence:**
1. New connections are rejected
2. Existing connections are signaled to close
3. In-flight requests have timeout seconds to complete
4. Socket is closed (forces remaining connections closed)
5. Resources are freed

**Thread Safety:**
- Function is thread-safe
- Safe to call from different thread than krepis_quic_start()
- Calling multiple times with same handle may error

**Memory Management:**
- Frees kernel-allocated server handle
- Releases TLS resources
- Closes all buffers associated with server

**Example Usage (TypeScript):**
```typescript
const response = await kernelFFI.symbols.krepis_quic_stop(serverHandle);

if (response.error_code === 0) {
  console.log("Server stopped successfully");
} else {
  console.error(`Stop failed: ${KrepisError.message(response.error_code)}`);
}
```

---

### krepis_quic_get_stats

Get current statistics from a running QUIC server.

**Signature:**
```c
FfiResponse krepis_quic_get_stats(uint64_t server_handle);
```

**Parameters:**
- `server_handle` (u64): Handle returned by krepis_quic_start()

**Returns:** FfiResponse
- `error_code`: 0 on success, KrepisError code on failure
- `result_buffer`: Contains serialized statistics

**Success Response:**
```
error_code: 0
result_buffer:
  data: <pointer to serialized stats buffer>
  len: <size of stats data>
  cap: <total capacity of stats buffer>
```

**Stats Format (Protobuf/JSON):**

The result_buffer contains serialized statistics. Format can be:
- **Protobuf:** Compact binary format (recommended for performance)
- **JSON:** Text format (easier debugging)

**Statistics Schema:**
```protobuf
message QuicServerStats {
  uint64 total_requests = 1;           // Cumulative request count
  uint32 active_connections = 2;       // Currently open connections
  uint64 total_bytes_in = 3;          // Bytes received from clients
  uint64 total_bytes_out = 4;         // Bytes sent to clients
  double avg_latency_ms = 5;          // Average request latency
  uint64 error_count = 6;             // Cumulative errors
  uint64 uptime_ms = 7;               // Time since server started
}
```

**Possible Errors:**
- `KrepisError::InvalidPointer` (1004): Handle is invalid
- `KrepisError::Internal` (1000): Failed to collect statistics

**Side Effects:**
- Collects current metrics from server
- Allocates buffer for serialized data
- Buffer remains valid until next FFI call

**Memory Management:**
- Kernel manages stats buffer
- Caller must not free returned buffer
- Buffer is invalidated on next FFI call

**Thread Safety:**
- Function is thread-safe
- Can be called while server is accepting requests
- Statistics collected atomically

**Example Usage (TypeScript):**
```typescript
const response = await kernelFFI.symbols.krepis_quic_get_stats(serverHandle);

if (response.error_code === 0) {
  const statsBuffer = response.result_buffer;
  const statsData = new Uint8Array(
    Deno.UnsafePointerView.getArrayBuffer(statsBuffer.data, statsBuffer.len)
  );
  
  // Deserialize protobuf/JSON
  const stats = deserializeStats(statsData);
  console.log(`Active connections: ${stats.activeConnections}`);
  console.log(`Avg latency: ${stats.avgLatencyMs.toFixed(2)}ms`);
} else {
  console.error(`Get stats failed: ${KrepisError.message(response.error_code)}`);
}
```

## Error Codes

All FFI functions return errors using the KrepisError enumeration:

| Code | Name | Retryable | Meaning |
|------|------|-----------|---------|
| 0 | Success | N/A | Operation succeeded |
| 1000 | Internal | No | Internal server error |
| 1001 | InvalidContext | No | Invalid context |
| 1004 | InvalidPointer | No | Null or invalid pointer |
| 4001 | InvalidRequest | No | Configuration is invalid |
| 5000 | NetworkError | Yes | Network operation failed |
| 2000 | Timeout | Yes | Operation exceeded timeout |

## ABI Compatibility

### Alignment

- **FfiQuicConfig**: 8-byte aligned (cacheline friendly)
- **FfiResponse**: 8-byte aligned
- **FfiBuffer**: 8-byte aligned
- All pointers are 64-bit (8 bytes on 64-bit systems)

### Endianness

- **Native endianness**: Structures use CPU native byte order
- **String buffers**: UTF-8 encoded, null-terminated

### Calling Convention

- **Platform**: x86_64 / ARM64
- **ABI**: System V AMD64 (Unix) or x64 (Windows)
- **Stack alignment**: 16-byte aligned on function entry

## Security Considerations

### TLS Certificates

- Certificate and key paths must be readable by server process
- Paths are validated before loading
- Invalid certificates will fail startup
- Keys must be unencrypted (passphrase not supported)

### Input Validation

All inputs are validated:
- Port range: 1-65535
- Max streams: > 0
- Timeout: >= 1000ms
- Buffer pointers: Must be valid and readable
- Handle values: Must reference active server

### Memory Safety

- All pointer operations are bounds-checked
- Buffer overflows impossible via FFI
- Kernel isolates server instances

## Performance Considerations

### Latency

- `krepis_quic_start()`: 1-10ms (TLS load time)
- `krepis_quic_stop()`: 1-100ms (graceful drain)
- `krepis_quic_get_stats()`: < 1ms (atomic snapshot)

### Throughput

- Single server can handle 100k+ connections
- Max streams per connection: Configurable (default 1000)
- Bytes in/out: Limited by network interface

### Memory

- Per-connection overhead: ~10-20KB
- Per-stream overhead: ~1-2KB
- Config buffer: 112 bytes (stack-allocated)

## Testing & Validation

### Unit Tests (Rust)

```bash
cargo test --lib krepis_core::abi
cargo test --lib krepis_core::quic_ffi
```

### Integration Tests (Deno)

```bash
deno test --allow-ffi adapter-tests.ts
```

### Validation Checklist

- [ ] Config pointer is valid and aligned
- [ ] Buffer paths are readable
- [ ] Port is available
- [ ] TLS certificates are valid
- [ ] Server handle is returned correctly
- [ ] Stop with valid handle succeeds
- [ ] Stats are returned correctly
- [ ] Multiple servers can coexist

## Version History

### v1.1.0 (Current)

- Initial QUIC FFI specification
- Three functions: start, stop, get_stats
- FfiQuicConfig structure
- Handle-based server management

## References

- QUIC RFC 9000: https://tools.ietf.org/html/rfc9000
- Krepis Core ABI: `crates/krepis-core/src/abi.rs`
- KNUL Adapter: `packages/deno-krepis-knul/adapter.ts`