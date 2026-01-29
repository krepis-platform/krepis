/**
 * Krepis Core - TypeScript FFI Binding Examples
 *
 * Demonstrates proper usage of zero-copy bindings with resource management.
 */

import {
  loadKrepisCore,
  FfiBuffer,
  FfiResponse,
  SharedMemoryMetadata,
  KrepisError,
  getKrepisErrorMessage,
  isKrepisErrorRetryable,
  isKrepisErrorResourceError,
  createContext,
  serializeContext,
  deserializeContext,
  type IKrepisContext,
} from "./mod.ts";

// ============================================================================
// EXAMPLE 1: Initialize Library
// ============================================================================

export function initializeKrepisLibrary(libPath?: string): void {
  console.log("Loading Krepis Core library...");
  const lib = libPath ? loadKrepisCore(libPath) : loadKrepisCore();
  console.log("✓ Krepis Core library loaded successfully");
  console.log("  Symbols available:", Object.keys(lib.symbols).join(", "));
}

// ============================================================================
// EXAMPLE 2: Working with FfiBuffer
// ============================================================================

/**
 * Example: Create and manage FfiBuffer with automatic disposal
 *
 * IMPORTANT: Always use `using` or try/finally for resource cleanup
 */
export function exampleFfiBuffer(bufferPtr: Deno.PointerValue): void {
  if (bufferPtr === null) {
    console.error("Buffer pointer is null");
    return;
  }

  // Using explicit scope (TS 5.2+) with Symbol.dispose
  using buffer = new FfiBuffer(bufferPtr);

  console.log("Buffer information:");
  console.log(`  - data pointer: ${formatPointer(buffer.data)}`);
  console.log(`  - length: ${buffer.len}`);
  console.log(`  - capacity: ${buffer.cap}`);
  console.log(`  - valid: ${buffer.isValid()}`);

  // buffer is automatically freed when exiting this scope
}

/**
 * Manual resource management (if `using` is not available)
 */
export function exampleFfiBufferManual(bufferPtr: Deno.PointerValue): void {
  if (bufferPtr === null) {
    console.error("Buffer pointer is null");
    return;
  }

  const buffer = new FfiBuffer(bufferPtr);

  try {
    console.log("Processing buffer...");
    console.log(`  - size: ${buffer.len} bytes`);
    console.log(`  - capacity: ${buffer.cap} bytes`);

    // Process buffer contents...
  } finally {
    // Explicitly dispose when done
    buffer[Symbol.dispose]();
  }
}

// ============================================================================
// EXAMPLE 3: Working with FfiResponse
// ============================================================================

/**
 * Example: Handle FFI response with error checking
 */
export function exampleFfiResponse(responsePtr: Deno.PointerValue): void {
  if (responsePtr === null) {
    console.error("Response pointer is null");
    return;
  }

  using response = new FfiResponse(responsePtr);

  if (response.isError()) {
    console.error(`✗ Request failed: ${response.getErrorMessage()}`);
    const errorCode = response.errorCode;

    if (isKrepisErrorRetryable(errorCode)) {
      console.log("  → Error is retryable, consider retry strategy");
    }

    if (isKrepisErrorResourceError(errorCode)) {
      console.log("  → Resource exhaustion detected");
    }
  } else {
    console.log("✓ Request succeeded");

    // Access result buffer (also has automatic disposal)
    using resultBuffer = response.resultBufferMut;
    console.log(`  - result size: ${resultBuffer.len} bytes`);
    console.log(`  - result capacity: ${resultBuffer.cap} bytes`);
  }
}

// ============================================================================
// EXAMPLE 4: Working with SovereignContext
// ============================================================================

/**
 * Example: Create and serialize context
 */
export function exampleContextCreation(): IKrepisContext {
  const ctx = createContext(
    "req-12345",      // requestId
    "tenant-acme",    // tenantId
    "trace-xyz789",   // traceId
    false,            // isTurboMode (standard FFI)
  );

  console.log("Created context:");
  console.log(`  - request ID: ${ctx.requestId}`);
  console.log(`  - tenant ID: ${ctx.tenantId}`);
  console.log(`  - trace ID: ${ctx.traceId}`);
  console.log(`  - turbo mode: ${ctx.isTurboMode}`);
  console.log(`  - timestamp: ${ctx.timestamp}ns`);

  return ctx;
}

/**
 * Example: Serialize context for FFI call
 */
export function exampleContextSerialization(ctx: IKrepisContext): string {
  const json = serializeContext(ctx);
  console.log("Serialized context:");
  console.log(`  ${json}`);
  return json;
}

/**
 * Example: Deserialize response context
 */
export function exampleContextDeserialization(json: string): IKrepisContext {
  const ctx = deserializeContext(json);
  console.log("Deserialized context:");
  console.log(`  - request ID: ${ctx.requestId}`);
  console.log(`  - tenant ID: ${ctx.tenantId}`);
  return ctx;
}

/**
 * Example: Create turbo-mode context for shared memory
 */
export function exampleTurboContext(): IKrepisContext {
  return createContext(
    "req-turbo-456",
    "tenant-premium",
    "trace-fast-path",
    true, // Enable turbo mode for zero-copy
  );
}

// ============================================================================
// EXAMPLE 5: Working with SharedMemoryMetadata
// ============================================================================

/**
 * Example: Read shared memory metadata
 */
export function exampleSharedMemoryMetadata(metadataPtr: Deno.PointerValue): void {
  if (metadataPtr === null) {
    console.error("Metadata pointer is null");
    return;
  }

  const metadata = new SharedMemoryMetadata(metadataPtr);

  console.log("Shared Memory Metadata:");
  console.log(`  - version: ${metadata.version}`);
  console.log(`  - lock state: ${metadata.lockState}`);
  console.log(`  - kernel timestamp: ${metadata.kernelTs}ns`);
  console.log(`  - SDK timestamp: ${metadata.sdkTs}ns`);
  console.log(`  - data offset: ${metadata.dataOffset}`);
  console.log(`  - data size: ${metadata.dataSize}`);
  console.log(`  - valid: ${metadata.isValid()}`);
}

/**
 * Example: Update lock state in shared memory
 */
export function exampleUpdateLockState(metadataPtr: Deno.PointerValue): void {
  if (metadataPtr === null) {
    console.error("Metadata pointer is null");
    return;
  }

  const metadata = new SharedMemoryMetadata(metadataPtr);

  console.log(`Current lock state: ${metadata.lockState}`);

  // Update to indicate SDK ownership
  metadata.lockState = SharedMemoryMetadata.SDK_OWNED;
  metadata.sdkTs = BigInt(Date.now()) * 1_000_000n;

  console.log(`Updated lock state: ${metadata.lockState}`);
}

// ============================================================================
// EXAMPLE 6: Error Handling
// ============================================================================

/**
 * Example: Comprehensive error handling
 */
export function exampleErrorHandling(errorCode: number): void {
  const code = errorCode as KrepisError;

  console.log(
    `Error: ${getKrepisErrorMessage(code)} (0x${code.toString(16).padStart(4, "0")})`,
  );

  if (code === KrepisError.Success) {
    console.log("✓ Operation succeeded");
  } else if (isKrepisErrorRetryable(code)) {
    console.log("⟳ Error is retryable - implement exponential backoff");
  } else if (isKrepisErrorResourceError(code)) {
    console.log("⚠ Resource exhaustion - trigger cleanup/scaling");
  } else {
    console.log("✗ Permanent error - check context and request validity");
  }
}

// ============================================================================
// EXAMPLE 7: Full Integration Flow
// ============================================================================

/**
 * Example: Complete request flow with proper resource management
 */
export async function exampleFullIntegrationFlow(libPath?: string): Promise<void> {
  // Step 1: Load library
  initializeKrepisLibrary(libPath);

  // Step 2: Create context
  const context = exampleContextCreation();
  const contextJson = exampleContextSerialization(context);

  // Step 3: Simulate FFI call (would normally call kernel functions here)
  console.log("\n--- Simulated FFI Call ---");
  console.log(`Sending request with context: ${context.requestId}`);

  // Step 4: Handle response (in real code, this comes from FFI)
  console.log("\n--- Response Handling ---");
  console.log("(In production, would receive actual response pointer)");

  // Step 5: Check error codes
  exampleErrorHandling(KrepisError.Success);

  console.log("\n✓ Integration flow complete");
}

// ============================================================================
// EXAMPLE 8: Turbo Mode (Zero-Copy Shared Memory)
// ============================================================================

/**
 * Example: Turbo mode workflow
 */
export function exampleTurboModeFlow(sharedMemPtr: Deno.PointerValue): void {
  if (sharedMemPtr === null) {
    console.error("Shared memory pointer is null");
    return;
  }

  console.log("=== TURBO MODE (Zero-Copy) ===\n");

  // Step 1: Access shared memory metadata
  const metadata = new SharedMemoryMetadata(sharedMemPtr);
  console.log(`Shared memory version: ${metadata.version}`);

  // Step 2: Create turbo context
  const turboCtx = exampleTurboContext();
  console.log(`✓ Turbo context created (isTurboMode=${turboCtx.isTurboMode})`);

  // Step 3: Coordinate lock state
  console.log(`\nLock negotiation:`);
  console.log(`  Current state: ${metadata.lockState}`);

  if (metadata.lockState === SharedMemoryMetadata.KERNEL_OWNED) {
    console.log("  → Kernel owns, we can read");
  } else if (metadata.lockState === SharedMemoryMetadata.SDK_OWNED) {
    console.log("  → SDK owns, kernel can read");
  }

  // Step 4: Read/write data from/to shared buffer (zero-copy)
  console.log(`\nShared memory region: offset=${metadata.dataOffset}, size=${metadata.dataSize}`);
}

// ============================================================================
// EXAMPLE 9: Batch Operations with Resource Management
// ============================================================================

/**
 * Example: Process multiple buffers with proper cleanup
 */
export function exampleBatchProcessing(bufferPtrs: Deno.PointerValue[]): void {
  if (bufferPtrs.length === 0) {
    console.log("No buffers to process");
    return;
  }

  console.log(`Processing ${bufferPtrs.length} buffers...\n`);

  const buffers: FfiBuffer[] = [];

  try {
    // Create all buffers
    for (const ptr of bufferPtrs) {
      if (ptr !== null) {
        buffers.push(new FfiBuffer(ptr));
      }
    }

    // Process batch
    let totalSize = 0n;
    for (let i = 0; i < buffers.length; i++) {
      const buf = buffers[i];
      if (buf && buf.isValid()) {
        totalSize += buf.len;
        console.log(`  [${i}] size=${buf.len}, capacity=${buf.cap}`);
      }
    }

    console.log(`\nTotal size: ${totalSize} bytes`);
  } finally {
    // Clean up all buffers
    for (const buf of buffers) {
      if (buf) {
        buf[Symbol.dispose]();
      }
    }
  }
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Format pointer for display
 * Safely handles both PointerObject and null PointerValue
 */
function formatPointer(ptr: Deno.PointerValue): string {
  if (ptr === null) return "null";
  // ptr is PointerObject here (non-null)
  const val = Deno.UnsafePointer.value(ptr);
  return `0x${val.toString(16)}`;
}

// ============================================================================
// RUN EXAMPLES
// ============================================================================

if (import.meta.main) {
  console.log("Krepis Core FFI Binding Examples\n");
  console.log("================================\n");

  // Initialize (would need actual library path)
  console.log("Note: Actual FFI calls require valid library path.\n");

  // Run examples
  console.log("Example 1: Context Creation");
  exampleContextCreation();
  console.log();

  console.log("Example 2: Context Serialization");
  const ctx = exampleContextCreation();
  const json = exampleContextSerialization(ctx);
  console.log();

  console.log("Example 3: Context Deserialization");
  exampleContextDeserialization(json);
  console.log();

  console.log("Example 4: Turbo Context");
  exampleTurboContext();
  console.log();

  console.log("Example 5: Error Code Handling");
  exampleErrorHandling(KrepisError.QuotaExceeded);
  console.log();

  console.log("✓ All examples completed");
}