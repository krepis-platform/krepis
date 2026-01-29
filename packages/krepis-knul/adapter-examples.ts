/**
 * Krepis KNUL - Adapter Usage Examples
 *
 * Demonstrates proper usage of the adapter layer with explicit context
 * propagation and binary-first payload handling.
 */

import {
    AdapterBuilder,
    AdapterProtocol,
    createAdapter,
    type QuicConfig,
    type IAdapter,
    type AdapterConfig,
  } from "./adapter.ts";
  
  import { createContext } from "../krepis-core/mod.ts";
  import type { IKrepisContext } from "../krepis-core/mod.ts";
  
  // ============================================================================
  // EXAMPLE 1: Create QUIC Adapter with Builder Pattern
  // ============================================================================
  
  export function exampleQuicAdapterBuilder(): IAdapter {
    console.log("=== Example 1: QUIC Adapter Builder ===\n");
  
    const adapter = new AdapterBuilder()
      .protocol(AdapterProtocol.QUIC)
      .host("127.0.0.1")
      .port(4433)
      .certPath("./certs/server.crt")
      .keyPath("./certs/server.key")
      .maxConnections(5000)
      .requestTimeoutMs(30000)
      .maxPayloadBytes(10 * 1024 * 1024) // 10MB
      .build();
  
    console.log("✓ QUIC adapter created");
    const config = adapter.getConfig();
    console.log(`  - Host: ${config.host}:${config.port}`);
    console.log(`  - Max Connections: ${config.maxConnections}`);
    console.log(`  - Max Payload: ${config.maxPayloadBytes} bytes`);
    console.log();
  
    return adapter;
  }
  
  // ============================================================================
  // EXAMPLE 2: Create QUIC Adapter with Direct Configuration
  // ============================================================================
  
  export function exampleQuicAdapterDirect(): IAdapter {
    console.log("=== Example 2: QUIC Adapter Direct Configuration ===\n");
  
    const config: QuicConfig = {
      protocol: AdapterProtocol.QUIC,
      host: "0.0.0.0",
      port: 4433,
      certPath: "./certs/server.crt",
      keyPath: "./certs/server.key",
      maxConnections: 10000,
      requestTimeoutMs: 60000,
      maxPayloadBytes: 50 * 1024 * 1024, // 50MB
      idleTimeoutMs: 120000,
      maxStreamsConcurrent: 1000,
      requireClientAuth: false,
    };
  
    const adapter = createAdapter(config);
  
    console.log("✓ QUIC adapter created with custom config");
    console.log(`  - Bind all interfaces: ${config.host}`);
    console.log(`  - Idle timeout: ${config.idleTimeoutMs}ms`);
    console.log();
  
    return adapter;
  }
  
  // ============================================================================
  // EXAMPLE 3: Adapter Lifecycle (Start/Stop)
  // ============================================================================
  
  export async function exampleAdapterLifecycle(): Promise<void> {
    console.log("=== Example 3: Adapter Lifecycle ===\n");
  
    const adapter = new AdapterBuilder()
      .protocol(AdapterProtocol.QUIC)
      .host("127.0.0.1")
      .port(4434) // Different port to avoid conflicts
      .certPath("./certs/server.crt")
      .keyPath("./certs/server.key")
      .build();
  
    try {
      // Start adapter
      console.log("Starting adapter...");
      await adapter.start();
      console.log("✓ Adapter started\n");
  
      // Check running state
      console.log(`Running: ${adapter.isRunning()}`);
      console.log();
  
      // Get initial stats
      const stats = adapter.getStats();
      console.log("Initial Stats:");
      console.log(`  - Total Requests: ${stats.totalRequests}`);
      console.log(`  - Active Connections: ${stats.activeConnections}`);
      console.log(`  - Uptime: ${stats.uptimeMs}ms`);
      console.log();
  
      // Simulate server running...
      console.log("(Adapter would accept connections here)");
      console.log();
  
      // Stop adapter
      console.log("Stopping adapter...");
      await adapter.stop();
      console.log("✓ Adapter stopped\n");
  
      console.log(`Running: ${adapter.isRunning()}`);
    } catch (error) {
      console.error(`Adapter error: ${error}`);
    }
  }
  
  // ============================================================================
  // EXAMPLE 4: Request Context Propagation
  // ============================================================================
  
  export async function exampleContextPropagation(): Promise<void> {
    console.log("=== Example 4: Context Propagation ===\n");
  
    // Create a request context
    const ctx = createContext(
      "req-abc123",        // requestId
      "tenant-acme",       // tenantId
      "trace-xyz789",      // traceId
      false,               // isTurboMode (standard FFI)
    );
  
    console.log("Created Request Context:");
    console.log(`  - Request ID: ${ctx.requestId}`);
    console.log(`  - Tenant ID: ${ctx.tenantId}`);
    console.log(`  - Trace ID: ${ctx.traceId}`);
    console.log(`  - Turbo Mode: ${ctx.isTurboMode}`);
    console.log(`  - Timestamp: ${ctx.timestamp}ns`);
    console.log();
  
    // Context is passed through all async operations
    console.log("Context flows through:");
    console.log("  1. Incoming network request → ctx");
    console.log("  2. Adapter.handle(ctx, payload)");
    console.log("  3. Kernel FFI call with ctx");
    console.log("  4. Response includes result from ctx operation");
    console.log();
  
    // Example: child context for spawned operations
    const childCtx = ctx;
    childCtx.isTurboMode = true;
  
    console.log("Modified Context (child operation):");
    console.log(`  - Turbo Mode: ${childCtx.isTurboMode}`);
    console.log(`  - Trace ID (preserved): ${childCtx.traceId}`);
  }
  
  // ============================================================================
  // EXAMPLE 5: Binary Payload Handling
  // ============================================================================
  
  export function exampleBinaryPayload(): void {
    console.log("=== Example 5: Binary Payload Handling ===\n");
  
    // Create binary payload (e.g., serialized protobuf/msgpack)
    const payload = new Uint8Array([
      0x01, 0x02, 0x03, 0x04, // Header
      0x05, 0x06, 0x07, 0x08, // Body
      0x09, 0x0a, 0x0b, 0x0c, // Trailer
    ]);
  
    console.log("Binary Payload (Uint8Array):");
    console.log(`  - Size: ${payload.length} bytes`);
    console.log(`  - Hex: ${Array.from(payload).map((b) => b.toString(16).padStart(2, "0")).join(" ")}`);
    console.log();
  
    // Create context for this request
    const ctx = createContext(
      "req-binary-001",
      "tenant-acme",
      "trace-binary-xyz",
    );
  
    console.log("Adapter Usage (pseudocode):");
    console.log(`
  async handle(ctx: IKrepisContext, payload: Uint8Array) {
    // 1. Context is explicit parameter - no global state
    // 2. Payload is Uint8Array - binary-first
    // 3. No copying of payload unless required by protocol
    
    // Validate payload size
    if (payload.length > this.config.maxPayloadBytes) {
      throw new Error("Payload too large");
    }
    
    // Forward to kernel FFI with binary payload
    // Kernel processes payload efficiently
    const response = await kernelFFI(ctx, payload);
    
    // Return FfiResponse (error code + result buffer)
    return response;
  }
    `);
    console.log();
  
    console.log("Memory Efficiency:");
    console.log("  ✓ Payload passed as reference (Uint8Array)");
    console.log("  ✓ No serialization/deserialization overhead");
    console.log("  ✓ Context propagated explicitly (not global)");
    console.log("  ✓ Direct FFI boundary crossing");
  }
  
  // ============================================================================
  // EXAMPLE 6: Statistics Monitoring
  // ============================================================================
  
  export async function exampleStatisticsMonitoring(): Promise<void> {
    console.log("=== Example 6: Statistics Monitoring ===\n");
  
    const adapter = new AdapterBuilder()
      .protocol(AdapterProtocol.QUIC)
      .host("127.0.0.1")
      .port(4435)
      .certPath("./certs/server.crt")
      .keyPath("./certs/server.key")
      .build();
  
    try {
      await adapter.start();
  
      // Simulate some activity
      console.log("Adapter running, simulating activity...\n");
  
      // Get stats periodically
      const stats = adapter.getStats();
  
      console.log("Adapter Statistics:");
      console.log(`  - Total Requests: ${stats.totalRequests}`);
      console.log(`  - Active Connections: ${stats.activeConnections}`);
      console.log(`  - Total Bytes In: ${stats.totalBytesIn}`);
      console.log(`  - Total Bytes Out: ${stats.totalBytesOut}`);
      console.log(`  - Average Latency: ${stats.avgLatencyMs.toFixed(2)}ms`);
      console.log(`  - Error Count: ${stats.errorCount}`);
      console.log(`  - Uptime: ${stats.uptimeMs}ms`);
      console.log();
  
      console.log("Stats are obtained from getStats() method:");
      console.log("  - Enables monitoring and health checks");
      console.log("  - No global state required");
      console.log("  - Per-adapter instance tracking");
  
      await adapter.stop();
    } catch (error) {
      console.error(`Error: ${error}`);
    }
  }
  
  // ============================================================================
  // EXAMPLE 7: Disposable Pattern
  // ============================================================================
  
  export async function exampleDisposablePattern(): Promise<void> {
    console.log("=== Example 7: Disposable Pattern ===\n");
  
    // Using async dispose (TS 5.2+ with 'await using')
    console.log("Async Dispose Pattern (preferred):");
    console.log(`
  await using adapter = new AdapterBuilder()
    .protocol(AdapterProtocol.QUIC)
    .host("127.0.0.1")
    .port(4436)
    .certPath("./certs/server.crt")
    .keyPath("./certs/server.key")
    .build();
  
  await adapter.start();
  
  // Use adapter...
  
  // Automatically calls [Symbol.asyncDispose]() when exiting scope
  // - Calls stop() if running
  // - Releases all resources
    `);
    console.log();
  
    console.log("Synchronous Dispose Pattern (fallback):");
    console.log(`
  using adapter = new AdapterBuilder()
    .protocol(AdapterProtocol.QUIC)
    .host("127.0.0.1")
    .port(4436)
    .certPath("./certs/server.crt")
    .keyPath("./certs/server.key")
    .build();
  
  // Note: Cannot call await adapter.start() in using block
  // Use await using for async operations
  
  // Automatically calls [Symbol.dispose]() when exiting scope
    `);
    console.log();
  
    console.log("Manual Pattern (least preferred):");
    console.log(`
  const adapter = new AdapterBuilder().build();
  try {
    await adapter.start();
    // Use adapter...
  } finally {
    await adapter[Symbol.asyncDispose]();  // Manual cleanup
  }
    `);
  }
  
  // ============================================================================
  // EXAMPLE 8: Protocol Agnostic Usage
  // ============================================================================
  
  export function exampleProtocolAgnostic(): void {
    console.log("=== Example 8: Protocol Agnostic Interface ===\n");
  
    // Same interface, different protocols
    const configs: AdapterConfig[] = [
      // QUIC config
      {
        protocol: AdapterProtocol.QUIC,
        host: "127.0.0.1",
        port: 4433,
        certPath: "./certs/server.crt",
        keyPath: "./certs/server.key",
        maxConnections: 5000,
        requestTimeoutMs: 30000,
        maxPayloadBytes: 10 * 1024 * 1024,
      } as QuicConfig,
    ];
  
    console.log("Creating adapters from different protocols:");
    for (const config of configs) {
      try {
        const adapter = createAdapter(config);
        console.log(`✓ ${config.protocol.toUpperCase()} adapter created`);
        console.log(`  - Interface: IAdapter (protocol-agnostic)`);
        console.log(`  - Config: ${JSON.stringify(config, null, 2)}`);
      } catch (error) {
        console.error(`Failed to create adapter: ${error}`);
      }
    }
  }
  
  // ============================================================================
  // RUN EXAMPLES
  // ============================================================================
  
  if (import.meta.main) {
    console.log("Krepis KNUL - Adapter Examples\n");
    console.log("===============================\n");
  
    // Run synchronous examples
    exampleQuicAdapterBuilder();
    exampleQuicAdapterDirect();
    exampleContextPropagation();
    exampleBinaryPayload();
    exampleProtocolAgnostic();
  
    // Note: Async examples require proper async context
    // In real usage, they would be in an async main() function:
    //
    // async function main() {
    //   await exampleAdapterLifecycle();
    //   await exampleStatisticsMonitoring();
    //   await exampleDisposablePattern();
    // }
    // main().catch(console.error);
  
    console.log("\n(Async examples skipped - see code for usage)");
    console.log(
      "\nFor async examples, run individual functions in proper async context",
    );
  }