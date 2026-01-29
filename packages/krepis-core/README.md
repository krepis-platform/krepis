# Krepis Core - Deno TypeScript FFI Bindings

Zero-copy FFI layer for Rust-Deno bridge with strict ABI compliance and explicit resource management.

## Features

- **Zero-Copy Data Transfer**: Direct pointer access via `Deno.UnsafePointerView`
- **Strict 8-Byte Alignment**: All structures maintain 64-bit system alignment
- **Explicit Resource Management**: `Disposable` interface with `Symbol.dispose`
- **Type-Safe Error Handling**: `KrepisError` enum with helper methods
- **Turbo Mode Support**: Zero-copy shared memory coordination
- **Memory Safety**: All pointers validated, automatic cleanup on disposal

## Module Structure

```
mod.ts               # Core FFI bindings and types
examples.ts          # Usage examples and patterns
deno.json           # Deno configuration
README.md           # This file
```

## Quick Start

### 1. Load the Library

```typescript
import { loadKrepisCore } from "@krepis/core";

// Load native library (adjust path as needed)
const lib = loadKrepisCore("./target/release/libkrepis_core.so");
```

### 2. Create and Manage Buffers

```typescript
import { FfiBuffer } from "@krepis/core";

// Using explicit resource management (TS 5.2+)
using buffer = new FfiBuffer(bufferPtr);

console.log(`Length: ${buffer.len}, Capacity: ${buffer.cap}`);
console.log(`Valid: ${buffer.isValid()}`);

// Automatically freed when exiting scope
```

### 3. Handle Responses

```typescript
import { FfiResponse, KrepisError, getKrepisErrorMessage, isKrepisErrorRetryable } from "@krepis/core";

if (responsePtr === null) {
  console.error("Response pointer is null");
} else {
  using response = new FfiResponse(responsePtr);

  if (response.isError()) {
    const err = response.errorCode;
    console.error(`Error: ${getKrepisErrorMessage(err)}`);

    if (isKrepisErrorRetryable(err)) {
      // Implement retry logic
    }
  } else {
    using result = response.resultBufferMut;
    // Process result...
  }
}
```

### 4. Work with Context

```typescript
import { createContext, serializeContext } from "@krepis/core";

// Create context
const ctx = createContext(
  "req-12345",
  "tenant-acme",
  "trace-xyz",
  false, // Standard mode (not turbo)
);

// Serialize for FFI
const json = serializeContext(ctx);

// Pass to kernel via FFI call...
```

## Memory Layout Reference

### FfiBuffer (32 bytes, 8-byte aligned)

```
Offset  Type    Field     Bytes   Description
0x00    ptr     data      8       Pointer to buffer data
0x08    u64     len       8       Valid data length
0x10    u64     cap       8       Total capacity
0x18    u64     _padding  8       Reserved for future use
```

### FfiResponse (40 bytes, 8-byte aligned)

```
Offset  Type           Field          Bytes   Description
0x00    u32            error_code     4       Error code (0 = success)
0x04    u32            _reserved      4       Reserved
0x08    FfiBuffer      result_buffer  32      Embedded result buffer
```

### SharedMemoryMetadata (32 bytes, 8-byte aligned)

```
Offset  Type    Field       Bytes   Description
0x00    u32     version     4       Metadata format version
0x04    u32     lock_state  4       Synchronization lock state
0x08    u64     kernel_ts   8       Kernel's last write timestamp (ns)
0x10    u64     sdk_ts      8       SDK's last write timestamp (ns)
0x18    u32     data_offset 4       Offset to first data region
0x1C    u32     data_size   4       Usable size after metadata
```

## Resource Management

### Automatic Disposal Pattern (Recommended)

```typescript
// Using explicit resource management (TypeScript 5.2+)
using buffer = new FfiBuffer(ptr);
using response = new FfiResponse(ptr);

// Automatically disposed when scope exits
// [Symbol.dispose]() is called internally
```

### Manual Disposal Pattern

```typescript
const buffer = new FfiBuffer(ptr);

try {
  // Use buffer...
} finally {
  buffer[Symbol.dispose]();
}
```

### Important: Always Dispose

FFI pointers reference kernel-managed memory. Failure to dispose leads to memory leaks:

```typescript
// ✗ BAD: Memory leak!
const buffer = new FfiBuffer(ptr);
console.log(buffer.len);
// buffer never disposed

// ✓ GOOD: Proper cleanup
using buffer = new FfiBuffer(ptr);
console.log(buffer.len);
// Automatic disposal
```

## Error Handling

### Error Codes

All errors are `u32` FFI-compatible codes:

```typescript
import {
  KrepisError,
  getKrepisErrorMessage,
  isKrepisErrorRetryable,
  isKrepisErrorResourceError,
} from "@krepis/core";

// Check error category
if (isKrepisErrorRetryable(errorCode)) {
  // Implement exponential backoff
}

if (isKrepisErrorResourceError(errorCode)) {
  // Trigger cleanup or auto-scaling
}

// Get human-readable message
const msg = getKrepisErrorMessage(errorCode as KrepisError);
console.error(`Error: ${msg}`);
```

### Common Error Codes

| Code | Name | Retryable | Meaning |
|------|------|-----------|---------|
| 0 | `Success` | No | Operation succeeded |
| 1000 | `Internal` | No | Internal error |
| 2000 | `Timeout` | Yes | Operation timed out |
| 3000 | `QuotaExceeded` | No | Resource quota exceeded |
| 4000 | `HandshakeFailed` | No | ABI handshake failed |
| 5000 | `NetworkError` | Yes | Network communication failed |

See `mod.ts` for complete error code reference.

## Turbo Mode (Zero-Copy Shared Memory)

For high-performance scenarios, use turbo mode:

```typescript
import { createContext, SharedMemoryMetadata } from "@krepis/core";

// Create turbo context
const ctx = createContext(
  "req-fast",
  "tenant-premium",
  "trace-xyz",
  true, // Enable turbo mode
);

// Access shared memory metadata
const metadata = new SharedMemoryMetadata(sharedMemPtr);

// Coordinate with kernel
if (metadata.lockState === SharedMemoryMetadata.KERNEL_OWNED) {
  // We can safely read from shared memory
  const dataPtr = sharedMemPtr + metadata.dataOffset;
  // Direct zero-copy access to data
}
```

### Turbo Mode Lock States

```typescript
SharedMemoryMetadata.KERNEL_OWNED = 0  // Kernel phase
SharedMemoryMetadata.SDK_OWNED = 1     // SDK phase
SharedMemoryMetadata.LOCKED = 2        // Contention
```

## Pointer Arithmetic

For accessing embedded structures or relative offsets:

```typescript
// Calculate offset to embedded buffer in response
const bufPtr = Number(BigInt(responsePtr) + 8n);

using buffer = new FfiBuffer(bufPtr as Deno.PointerValue);
```

### Safe Embedded Pointer Access

For accessing embedded structures within larger memory regions:

```typescript
// Example: embedded FfiBuffer at offset 8 within FfiResponse
const responsePtr: Deno.PointerValue = /* ... */;

// Calculate offset to embedded structure
const pointerValue = Deno.UnsafePointer.value(responsePtr);
const embeddedOffset = pointerValue + 8n;
const embeddedPtr = Deno.UnsafePointer.create(embeddedOffset);

// Use embedded pointer
using embedded = new FfiBuffer(embeddedPtr);
```

## Alignment Requirements

All FFI operations require strict 8-byte (64-bit) alignment:

- `FfiBuffer`: 32 bytes, 8-byte aligned
- `FfiResponse`: 40 bytes, 8-byte aligned
- `SharedMemoryMetadata`: 32 bytes, 8-byte aligned

Kernel allocates all buffers on 8-byte boundaries. **Do not create misaligned pointers.**

## Permissions Required

The FFI module requires specific Deno permissions:

```bash
# Run with FFI permission
deno run --allow-ffi my_program.ts

# With read permission (for library files)
deno run --allow-ffi --allow-read my_program.ts

# With environment variables (for lib path)
deno run --allow-ffi --allow-env my_program.ts
```

Note: `deno lint` requires `--allow-unsafe-ffi` flag for FFI code analysis.

## Usage Examples

See `examples.ts` for comprehensive examples:

- Buffer creation and validation
- Response error handling
- Context serialization/deserialization
- Shared memory coordination
- Batch processing with resource management
- Full integration flow

Run examples:

```bash
deno run --allow-env examples.ts
```

## Type Safety

All types are strictly typed with TypeScript:

```typescript
import {
  FfiBuffer,
  FfiResponse,
  SharedMemoryMetadata,
  KrepisError,
  getKrepisErrorMessage,
  isKrepisErrorRetryable,
  isKrepisErrorResourceError,
  type IKrepisContext,
} from "@krepis/core";

// Context is properly typed
const ctx: IKrepisContext = createContext(...);

// Error codes are enum-typed
const code: KrepisError = response.errorCode;

// Error helpers are strongly typed
const msg = getKrepisErrorMessage(code);
const retryable = isKrepisErrorRetryable(code);
const resourceErr = isKrepisErrorResourceError(code);
```

## Performance Considerations

### Zero-Copy Access

```typescript
// Direct pointer access (zero-copy)
const dataPtr = buffer.data;

// No cloning, no serialization overhead
// Direct memory view of kernel-managed buffer
```

### Lazy View Initialization

`Deno.UnsafePointerView` is created on-demand:

```typescript
// First access creates view
const len1 = buffer.len; // Creates view

// Subsequent accesses reuse view
const len2 = buffer.len; // Reuses cached view

// Disposed when buffer[Symbol.dispose]() called
```

### Batch Operations

```typescript
// Efficiently process multiple buffers
const buffers = ptrs.map(p => new FfiBuffer(p));
try {
  // Process all buffers...
} finally {
  buffers.forEach(b => b[Symbol.dispose]());
}
```

## Troubleshooting

### "FfiBuffer has been disposed"

Accessing disposed buffer. Check resource scope:

```typescript
let buffer: FfiBuffer;
{
  using buf = new FfiBuffer(ptr);
  buffer = buf; // Reference escapes scope
}
// buffer is disposed here, but we're still trying to use it
```

### Library not found

Adjust library path for your build:

```typescript
// Linux
loadKrepisCore("./target/release/libkrepis_core.so")

// macOS
loadKrepisCore("./target/release/libkrepis_core.dylib")

// Windows
loadKrepisCore("./target/release/krepis_core.dll")
```

### Invalid pointer

Ensure pointer is valid FFI pointer and 8-byte aligned:

```typescript
// ✓ Valid pointer from kernel FFI call
const buffer = new FfiBuffer(kernelPtr);

// ✗ Invalid
const buffer = new FfiBuffer(null); // TypeError
```

## Testing

Run tests with FFI permission:

```bash
deno test --allow-ffi mod_test.ts
```

## ABI Version

Current ABI version: **1.1.0** (packed as `0x00010001`)

Check version compatibility:

```typescript
import { FFI_ABI_VERSION } from "@krepis/core";

console.log(`ABI Version: 0x${FFI_ABI_VERSION.toString(16)}`);
```

## Contributing

This module is auto-generated from Rust FFI definitions. Do not edit manually.

To regenerate:

1. Update Rust code in `crates/krepis-core/`
2. Run code generation tool
3. Commit both Rust and TypeScript

## License

Apache 2.0 (matching Krepis project license)

## Further Reading

- [Deno FFI Documentation](https://docs.deno.com/runtime/manual/runtime/ffi_api/)
- [Krepis Core Rust Documentation](../../crates/krepis-core/README.md)
- [Sovereign Bridge ABI Specification](../../docs/BRIDGE_ABI.md)