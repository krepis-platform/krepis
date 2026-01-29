# Krepis KNUL - Adapter Layer

Network adapter layer for bridging external requests to the Krepis kernel.

Implements protocol-agnostic request handling with:
- **Explicit Context Propagation**: All operations receive `IKrepisContext` parameter
- **Binary-First Design**: Efficient `Uint8Array` payload handling with minimal copying
- **Protocol Flexibility**: Support for HTTP, gRPC, QUIC via pluggable adapters
- **Resource Safety**: `Disposable` pattern for automatic cleanup

## Architecture

```
┌─────────────────────────┐
│   External Client       │
│  (HTTP/gRPC/QUIC)       │
└────────────┬────────────┘
             │ Binary Payload
             ▼
┌─────────────────────────┐
│   IAdapter Interface    │ ◄── Protocol-Agnostic
│  ├─ start()             │
│  ├─ stop()              │
│  ├─ handle()            │ ◄── Explicit Context
│  └─ getStats()          │
└────────────┬────────────┘
             │ IKrepisContext + Uint8Array
             ▼
┌─────────────────────────┐
│  Krepis Kernel FFI      │
│  (Rust Boundary)        │
└────────────┬────────────┘
             │ FfiResponse
             ▼
┌─────────────────────────┐
│   Response to Client    │
└─────────────────────────┘
```

## Core Concepts

### 1. Explicit Context (Deterministic Context Principle)

All request handling is bound to an explicit `IKrepisContext`:

```typescript
interface IKrepisContext {
  requestId: string;        // Unique request identifier
  tenantId: string;         // Multi-tenant isolation
  traceId: string;          // Distributed tracing
  isTurboMode: boolean;     // Zero-copy optimization flag
  timestamp: bigint;        // Request timestamp (ns)
}
```

**Why:** Eliminates implicit global state, enables determinism, aids debugging.

### 2. Binary-First Payloads

Adapters handle `Uint8Array` directly without serialization overhead:

```typescript
async handle(ctx: IKrepisContext, payload: Uint8Array): Promise<FfiResponse>
```

**Benefits:**
- No JSON overhead for binary protocols
- Direct FFI boundary crossing
- Efficient memory usage
- Protocol flexibility (protobuf, msgpack, etc.)

### 3. Protocol Agnostic

`IAdapter` interface works with any protocol:

```typescript
interface IAdapter {
  start(): Promise<void>;
  stop(): Promise<void>;
  handle(ctx: IKrepisContext, payload: Uint8Array): Promise<FfiResponse>;
  getStats(): AdapterStats;
  isRunning(): boolean;
}
```

Multiple protocol implementations share the same interface.

## Usage

### Basic Setup

```typescript
import {
  AdapterBuilder,
  AdapterProtocol,
  type IAdapter,
} from "@krepis/knul/adapter.ts";

// Create adapter with builder pattern
const adapter = new AdapterBuilder()
  .protocol(AdapterProtocol.QUIC)
  .host("127.0.0.1")
  .port(4433)
  .certPath("./certs/server.crt")
  .keyPath("./certs/server.key")
  .maxConnections(5000)
  .build();

// Start listening
await adapter.start();

// Use adapter...

// Graceful shutdown
await adapter.stop();
```

### With Disposable (Async Dispose)

```typescript
import { AdapterBuilder, AdapterProtocol } from "@krepis/knul/adapter.ts";

// TypeScript 5.2+ with 'await using'
await using adapter = new AdapterBuilder()
  .protocol(AdapterProtocol.QUIC)
  .host("127.0.0.1")
  .port(4433)
  .certPath("./certs/server.crt")
  .keyPath("./certs/server.key")
  .build();

await adapter.start();

// Automatic cleanup on scope exit
// Calls [Symbol.asyncDispose]() → stop()
```

### Request Handling with Context

```typescript
import {
  createContext,
  type IKrepisContext,
} from "@krepis/deno-krepis-core/mod.ts";

// Create context for incoming request
const ctx = createContext(
  "req-12345",      // requestId
  "tenant-acme",    // tenantId
  "trace-xyz",      // traceId
  false,            // isTurboMode
);

// Binary payload (e.g., from network)
const payload = new Uint8Array([
  0x01, 0x02, 0x03, 0x04,
  // ... serialized request data
]);

// Handle request with explicit context
try {
  const response = await adapter.handle(ctx, payload);

  if (response.isError()) {
    console.error(`Request failed: ${response.getErrorMessage()}`);
  } else {
    console.log(`Success`);
    using resultBuffer = response.resultBufferMut;
    // Process result...
  }
} catch (error) {
  console.error(`Adapter error: ${error}`);
}
```

## Configuration

### QUIC Configuration

```typescript
interface QuicConfig extends IAdapterConfig {
  protocol: AdapterProtocol.QUIC;
  host: string;
  port: number;
  certPath: string;              // TLS certificate
  keyPath: string;               // TLS private key
  caPath?: string;               // Optional: CA certificate
  requireClientAuth?: boolean;   // Optional: require client cert
  idleTimeoutMs?: number;        // Connection idle timeout
  maxStreamsConcurrent?: number; // Max concurrent streams
}
```

### HTTP/HTTPS Configuration

```typescript
interface HttpConfig extends IAdapterConfig {
  protocol: AdapterProtocol.HTTP | AdapterProtocol.HTTPS;
  certPath?: string;             // HTTPS only
  keyPath?: string;              // HTTPS only
  keepAliveTimeoutMs?: number;   // Keep-alive timeout
  httpVersion?: string;          // 1.1, 2.0, 3.0
}
```

### gRPC Configuration

```typescript
interface GrpcConfig extends IAdapterConfig {
  protocol: AdapterProtocol.GRPC;
  certPath?: string;
  keyPath?: string;
  enableReflection?: boolean;    // gRPC reflection
  maxMessageSize?: number;       // Message size limit
}
```

## Statistics & Monitoring

```typescript
interface AdapterStats {
  totalRequests: number;     // Cumulative request count
  activeConnections: number; // Current open connections
  totalBytesIn: number;      // Bytes received
  totalBytesOut: number;     // Bytes sent
  avgLatencyMs: number;      // Average request latency
  errorCount: number;        // Cumulative error count
  uptimeMs: number;          // Time since startup
}

// Get current statistics
const stats = adapter.getStats();
console.log(`Requests: ${stats.totalRequests}`);
console.log(`Avg Latency: ${stats.avgLatencyMs.toFixed(2)}ms`);
console.log(`Error Rate: ${(stats.errorCount / stats.totalRequests * 100).toFixed(2)}%`);
```

## Implementation Guide

### Creating a Custom Adapter

1. **Implement IAdapter interface**:
   ```typescript
   export class CustomAdapter implements IAdapter {
     async start(): Promise<void> { /* ... */ }
     async stop(): Promise<void> { /* ... */ }
     async handle(ctx: IKrepisContext, payload: Uint8Array): Promise<FfiResponse> { /* ... */ }
     getStats(): AdapterStats { /* ... */ }
     isRunning(): boolean { /* ... */ }
     getConfig(): AdapterConfig { /* ... */ }
   }
   ```

2. **Implement Disposable**:
   ```typescript
   [Symbol.asyncDispose](): Promise<void> {
     // Cleanup resources
   }

   [Symbol.dispose](): void {
     // Synchronous cleanup fallback
   }
   ```

3. **Handle context explicitly**:
   ```typescript
   async handle(ctx: IKrepisContext, payload: Uint8Array) {
     // Thread context through all operations
     // Use ctx.requestId, ctx.traceId for tracing
     // Use ctx.isTurboMode for optimization decisions
   }
   ```

4. **Register with factory** (optional):
   ```typescript
   export function createAdapter(config: AdapterConfig): IAdapter {
     switch (config.protocol) {
       case AdapterProtocol.CUSTOM:
         return new CustomAdapter(config);
       // ...
     }
   }
   ```

### QUIC Adapter Implementation

The QUIC adapter uses FFI functions from Krepis Core to manage the QUIC server:

```typescript
// Load kernel library
const kernelLib = loadKrepisCore("./libkrepis_core.so");

// Start QUIC server via FFI
async function startQuicServer(config: QuicConfig): Promise<u64> {
  const ffiConfig = createFfiQuicConfig(config);
  const response = kernelLib.symbols.krepis_quic_start(
    Deno.UnsafePointer.of(ffiConfig)
  );
  
  if (response.isError()) {
    throw new Error(`Failed to start server: ${response.getErrorMessage()}`);
  }
  
  // Extract server handle from response
  const handlePtr = response.resultBufferMut.data;
  const serverHandle = readU64FromFFI(handlePtr);
  return serverHandle;
}

// Stop QUIC server via FFI
async function stopQuicServer(serverHandle: u64): Promise<void> {
  const response = kernelLib.symbols.krepis_quic_stop(serverHandle);
  
  if (response.isError()) {
    throw new Error(`Failed to stop server: ${response.getErrorMessage()}`);
  }
}

// Get server statistics via FFI
async function getQuicServerStats(serverHandle: u64): Promise<QuicServerStats> {
  const response = kernelLib.symbols.krepis_quic_get_stats(serverHandle);
  
  if (response.isError()) {
    throw new Error(`Failed to get stats: ${response.getErrorMessage()}`);
  }
  
  // Deserialize stats from result buffer
  const statsBuffer = response.resultBufferMut;
  const statsData = new Uint8Array(
    Deno.UnsafePointerView.getArrayBuffer(statsBuffer.data, statsBuffer.len)
  );
  
  return deserializeQuicStats(statsData);
}
```

## Implementation Guide

## Best Practices

### 1. Always Use Context

```typescript
// ✗ BAD: No context
async handle(payload: Uint8Array) { }

// ✓ GOOD: Explicit context
async handle(ctx: IKrepisContext, payload: Uint8Array) {
  // context is traceable parameter
  // flows through all async operations
}
```

### 2. Binary-First Payloads

```typescript
// ✗ BAD: Unnecessary conversion
const json = JSON.parse(payloadString);
const binary = JSON.stringify(json);

// ✓ GOOD: Direct binary handling
async handle(ctx: IKrepisContext, payload: Uint8Array) {
  // Pass directly to kernel FFI
  const response = await kernelFFI(ctx, payload);
  return response;
}
```

### 3. Proper Resource Management

```typescript
// ✗ BAD: Resource leak
const adapter = new AdapterBuilder().build();
await adapter.start();
// ... adapter never stopped

// ✓ GOOD: Automatic cleanup
await using adapter = new AdapterBuilder().build();
await adapter.start();
// Automatically calls stop() on exit
```

### 4. Context Propagation in Async Chains

```typescript
async handle(ctx: IKrepisContext, payload: Uint8Array) {
  // ✓ Context flows through all operations
  const result1 = await operation1(ctx, payload);
  const result2 = await operation2(ctx, result1);
  const response = await operation3(ctx, result2);
  return response;
}
```

## Error Handling

```typescript
import { AdapterError } from "@krepis/knul/adapter.ts";

try {
  const response = await adapter.handle(ctx, payload);
  if (response.isError()) {
    // Handle kernel error
    console.error(`Kernel error: ${response.getErrorMessage()}`);
  }
} catch (error) {
  if (error instanceof AdapterError) {
    // Handle adapter error
    const code = error.code;          // Error code
    const retryable = error.retryable; // Can retry?
    console.error(`Adapter error (${code}): ${error.message}`);
  }
}
```

## Monitoring & Debugging

### Request Tracing

```typescript
// Context.traceId enables distributed tracing
const ctx = createContext(requestId, tenantId, traceId);

// Trace flows through:
// - Network adapter
// - Kernel FFI
// - Kernel execution
// - Result handling
```

### Performance Metrics

```typescript
const stats = adapter.getStats();

// Key metrics
const throughput = stats.totalRequests / (stats.uptimeMs / 1000);
const errorRate = stats.errorCount / stats.totalRequests;
const p99Latency = stats.avgLatencyMs * 2; // Approximation

console.log(`Throughput: ${throughput.toFixed(2)} req/s`);
console.log(`Error Rate: ${(errorRate * 100).toFixed(2)}%`);
console.log(`Est. P99: ${p99Latency.toFixed(2)}ms`);
```

## Lifecycle Events

### Startup Sequence

1. Create adapter with configuration
2. Call `start()` → binds to port, loads TLS, initializes listeners
3. Adapter ready to accept connections
4. `isRunning()` returns `true`

### Request Sequence

1. External client sends request
2. Adapter receives binary payload
3. Creates `IKrepisContext` from request metadata
4. Calls `handle(ctx, payload)`
5. Handler calls kernel FFI
6. Returns `FfiResponse` to client

### Shutdown Sequence

1. Call `stop()` or dispose adapter
2. Gracefully close active connections
3. Wait for in-flight requests (with timeout)
4. Release network resources
5. `isRunning()` returns `false`

## Protocol Support

| Protocol | Status | Config Type |
|----------|--------|-------------|
| QUIC | ✅ Skeleton | `QuicConfig` |
| HTTP | ⏳ Planned | `HttpConfig` |
| HTTPS | ⏳ Planned | `HttpConfig` |
| gRPC | ⏳ Planned | `GrpcConfig` |

## Type Safety

All types are strictly typed:

```typescript
import {
  type IAdapter,
  type AdapterConfig,
  type IAdapterConfig,
  type QuicConfig,
  type AdapterStats,
  AdapterProtocol,
  AdapterError,
} from "@krepis/knul/adapter.ts";
```

## Examples

See `adapter-examples.ts` for comprehensive examples:

```bash
deno run adapter-examples.ts
```

## API Reference

### AdapterBuilder

```typescript
class AdapterBuilder {
  protocol(p: AdapterProtocol): this;
  host(h: string): this;
  port(p: number): this;
  certPath(path: string): this;
  keyPath(path: string): this;
  maxConnections(max: number): this;
  requestTimeoutMs(ms: number): this;
  maxPayloadBytes(bytes: number): this;
  extra(options: Record<string, unknown>): this;
  build(): IAdapter;
}
```

### QuicAdapter

```typescript
class QuicAdapter implements IAdapter {
  constructor(config: QuicConfig);
  async start(): Promise<void>;
  async stop(): Promise<void>;
  async handle(ctx: IKrepisContext, payload: Uint8Array): Promise<FfiResponse>;
  getStats(): AdapterStats;
  isRunning(): boolean;
  getConfig(): QuicConfig;
  [Symbol.asyncDispose](): Promise<void>;
  [Symbol.dispose](): void;
}
```

### Factory Function

```typescript
function createAdapter(config: AdapterConfig): IAdapter;
```

## Performance Tuning

### Connection Pooling

```typescript
new AdapterBuilder()
  .maxConnections(10000)  // Adjust based on system capacity
  .build();
```

### Payload Size Limits

```typescript
new AdapterBuilder()
  .maxPayloadBytes(50 * 1024 * 1024)  // 50MB
  .build();
```

### Timeouts

```typescript
new AdapterBuilder()
  .requestTimeoutMs(60000)  // 60s timeout
  .build();
```

## Testing

```bash
# Run examples
deno run --allow-read adapter-examples.ts

# Type checking
deno check --strict adapter.ts

# Linting
deno lint adapter.ts
```

## Contributing

When adding new protocol support:

1. Create new adapter class implementing `IAdapter`
2. Register in `createAdapter()` factory
3. Add config interface
4. Implement lifecycle (`start`/`stop`)
5. Implement request handling with explicit context
6. Add tests and examples

## License

Apache 2.0 (matching Krepis project)