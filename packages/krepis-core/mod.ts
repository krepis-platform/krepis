/**
 * Krepis Core - Deno TypeScript FFI Bindings
 *
 * Zero-copy FFI layer for Rust-Deno bridge.
 * Strict 8-byte alignment on 64-bit systems.
 * Explicit Resource Management with Symbol.dispose
 */

// ============================================================================
// 1. FFI LIBRARY LOADING & SYMBOL DEFINITIONS
// ============================================================================

/**
 * Krepis Core FFI Library Interface
 * Maps Rust function signatures to Deno.dlopen
 */
interface KrepisCoreLib {
  symbols: {
    // Memory management
    free_buffer: (buffer_ptr: Deno.PointerValue) => void;
    // Timestamp utility (optional, for testing)
    get_timestamp_ns: () => bigint;
  };
}

/**
 * Global library instance (lazy-loaded)
 * Replace with actual library path in production
 */
let krepis_lib: KrepisCoreLib | null = null;

export function loadKrepisCore(
  libPath: string = "./target/release/libkrepis_core.so",
): KrepisCoreLib {
  if (krepis_lib) return krepis_lib;

  krepis_lib = Deno.dlopen(libPath, {
    free_buffer: { parameters: ["pointer"], result: "void" },
    get_timestamp_ns: { parameters: [], result: "u64" },
  }) as unknown as KrepisCoreLib;

  return krepis_lib;
}

export function getKrepisLib(): KrepisCoreLib {
  if (!krepis_lib) {
    throw new Error("Krepis library not loaded. Call loadKrepisCore() first.");
  }
  return krepis_lib;
}

// ============================================================================
// 2. KREPIS ERROR ENUM
// ============================================================================

/**
 * KrepisError - FFI-compatible error codes
 * Maps to Rust #[repr(u32)] enum
 */
export enum KrepisError {
  // === Success ===
  Success = 0,

  // === Internal Errors (0x1000-0x1FFF) ===
  Internal = 1000,
  InvalidContext = 1001,
  AbiMismatch = 1002,
  MemoryAlignment = 1003,
  InvalidPointer = 1004,

  // === Timeout Errors (0x2000-0x2FFF) ===
  Timeout = 2000,
  KernelTimeout = 2001,
  SdkTimeout = 2002,
  LockTimeout = 2003,

  // === Resource Errors (0x3000-0x3FFF) ===
  QuotaExceeded = 3000,
  OutOfMemory = 3001,
  CpuQuotaExceeded = 3002,
  ConcurrencyLimitExceeded = 3003,
  PoolExhausted = 3004,

  // === Validation Errors (0x4000-0x4FFF) ===
  HandshakeFailed = 4000,
  InvalidRequest = 4001,
  VersionMismatch = 4002,
  TenantNotFound = 4003,
  Unauthorized = 4004,

  // === Network Errors (0x5000-0x5FFF) ===
  NetworkError = 5000,
  ConnectionFailed = 5001,
  SerializationError = 5002,

  // === Domain-Specific Errors (0x6000-0x6FFF) ===
  VerificationError = 6000,
  IsolatePoolError = 6001,
  SchedulerError = 6002,
}

/**
 * Get error message from error code
 */
export function getKrepisErrorMessage(code: KrepisError): string {
  const messages: Record<KrepisError, string> = {
    [KrepisError.Success]: "Success",
    [KrepisError.Internal]: "Internal error",
    [KrepisError.InvalidContext]: "Invalid context",
    [KrepisError.AbiMismatch]: "ABI version mismatch",
    [KrepisError.MemoryAlignment]: "Memory alignment violation",
    [KrepisError.InvalidPointer]: "Invalid pointer",
    [KrepisError.Timeout]: "Operation timeout",
    [KrepisError.KernelTimeout]: "Kernel operation timeout",
    [KrepisError.SdkTimeout]: "SDK operation timeout",
    [KrepisError.LockTimeout]: "Lock acquisition timeout",
    [KrepisError.QuotaExceeded]: "Resource quota exceeded",
    [KrepisError.OutOfMemory]: "Out of memory",
    [KrepisError.CpuQuotaExceeded]: "CPU quota exceeded",
    [KrepisError.ConcurrencyLimitExceeded]: "Concurrency limit exceeded",
    [KrepisError.PoolExhausted]: "Connection pool exhausted",
    [KrepisError.HandshakeFailed]: "Handshake failed",
    [KrepisError.InvalidRequest]: "Invalid request",
    [KrepisError.VersionMismatch]: "Version mismatch",
    [KrepisError.TenantNotFound]: "Tenant not found",
    [KrepisError.Unauthorized]: "Unauthorized",
    [KrepisError.NetworkError]: "Network error",
    [KrepisError.ConnectionFailed]: "Connection failed",
    [KrepisError.SerializationError]: "Serialization error",
    [KrepisError.VerificationError]: "Verification error",
    [KrepisError.IsolatePoolError]: "Isolate pool error",
    [KrepisError.SchedulerError]: "Scheduler error",
  };
  return messages[code] ?? "Unknown error";
}

/**
 * Check if error is retryable
 */
export function isKrepisErrorRetryable(code: KrepisError): boolean {
  return [
    KrepisError.Timeout,
    KrepisError.KernelTimeout,
    KrepisError.SdkTimeout,
    KrepisError.LockTimeout,
    KrepisError.NetworkError,
    KrepisError.ConnectionFailed,
    KrepisError.PoolExhausted,
  ].includes(code);
}

/**
 * Check if error is a resource exhaustion issue
 */
export function isKrepisErrorResourceError(code: KrepisError): boolean {
  return [
    KrepisError.QuotaExceeded,
    KrepisError.OutOfMemory,
    KrepisError.CpuQuotaExceeded,
    KrepisError.ConcurrencyLimitExceeded,
    KrepisError.PoolExhausted,
  ].includes(code);
}

// ============================================================================
// 3. FFI BUFFER CLASS (Zero-Copy with Disposal)
// ============================================================================

/**
 * FfiBuffer - FFI-safe zero-copy buffer descriptor
 *
 * Memory Layout (32 bytes, 8-byte aligned):
 * - Offset 0: data (pointer, 8 bytes)
 * - Offset 8: len (u64, 8 bytes)
 * - Offset 16: cap (u64, 8 bytes)
 * - Offset 24: _padding (u64, 8 bytes)
 *
 * Implements Disposable for automatic resource cleanup
 */
export class FfiBuffer implements Disposable {
  private static readonly SIZE = 32; // 8 * 4 fields
  private static readonly ALIGN = 8;
  private static readonly OFFSET_DATA = 0;
  private static readonly OFFSET_LEN = 8;
  private static readonly OFFSET_CAP = 16;
  private static readonly OFFSET_PADDING = 24;

  /** Raw pointer to memory block (non-null PointerObject) */
  private pointer: Deno.PointerObject;

  /** Cached view for repeated access */
  private view: Deno.UnsafePointerView | null = null;

  private disposed = false;

  /**
   * Create FfiBuffer from existing pointer
   * @param pointer Pointer to FFI buffer memory (must be 8-byte aligned)
   */
  constructor(pointer: Deno.PointerValue) {
    if (pointer === null) {
      throw new TypeError("Invalid pointer: cannot be null");
    }
    // Safe cast: null is ruled out above, so this is PointerObject
    this.pointer = pointer as Deno.PointerObject;
  }

  /**
   * Get data pointer (at offset 0)
   * Returns null if data pointer is zero, otherwise returns PointerObject
   */
  get data(): Deno.PointerValue {
    this.assertNotDisposed();
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    // Read pointer value (8 bytes as BigUint64)
    const dataVal = this.view.getBigUint64(FfiBuffer.OFFSET_DATA);
    if (dataVal === 0n) return null;
    // Deno.UnsafePointer.create() returns PointerObject (non-null)
    const dataPtr = Deno.UnsafePointer.create(dataVal);
    return dataPtr; // PointerObject, never null
  }

  /**
   * Get length (at offset 8)
   */
  get len(): bigint {
    this.assertNotDisposed();
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getBigUint64(FfiBuffer.OFFSET_LEN);
  }

  /**
   * Get capacity (at offset 16)
   */
  get cap(): bigint {
    this.assertNotDisposed();
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getBigUint64(FfiBuffer.OFFSET_CAP);
  }

  /**
   * Get padding (at offset 24)
   */
  get padding(): bigint {
    this.assertNotDisposed();
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getBigUint64(FfiBuffer.OFFSET_PADDING);
  }

  /**
   * Direct pointer access for advanced use cases
   */
  getPointer(): Deno.PointerObject {
    this.assertNotDisposed();
    return this.pointer;
  }

  /**
   * Verify buffer validity
   */
  isValid(): boolean {
    this.assertNotDisposed();
    const dataPtr = this.data;
    const length = this.len;
    const capacity = this.cap;

    // Null buffer with zero len/cap is valid
    if (dataPtr === null) {
      return length === 0n && capacity === 0n;
    }

    // Non-null buffer must have capacity >= length
    return capacity >= length && length > 0n;
  }

  /**
   * Check if disposed
   */
  private assertNotDisposed(): void {
    if (this.disposed) {
      throw new ReferenceError("FfiBuffer has been disposed");
    }
  }

  /**
   * Explicit disposal (Disposable protocol)
   * Calls kernel's free_buffer FFI function
   */
  [Symbol.dispose](): void {
    if (this.disposed) return;
    this.disposed = true;
    this.view = null;

    try {
      const lib = getKrepisLib();
      lib.symbols.free_buffer(this.pointer);
    } catch (error) {
      console.error("Failed to free FfiBuffer:", error);
    }
  }
}

// ============================================================================
// 4. FFI RESPONSE CLASS (Composite with Disposal)
// ============================================================================

/**
 * FfiResponse - FFI response wrapper
 *
 * Memory Layout (40 bytes, 8-byte aligned):
 * - Offset 0: error_code (u32, 4 bytes)
 * - Offset 4: _reserved (u32, 4 bytes)
 * - Offset 8: result_buffer (FfiBuffer, 32 bytes)
 *
 * Implements Disposable to clean up result_buffer
 */
export class FfiResponse implements Disposable {
  private static readonly SIZE = 40;
  private static readonly ALIGN = 8;
  private static readonly OFFSET_ERROR_CODE = 0;
  private static readonly OFFSET_RESULT_BUFFER = 8;

  /** Raw pointer to memory block (non-null PointerObject) */
  private pointer: Deno.PointerObject;

  private view: Deno.UnsafePointerView | null = null;
  private resultBuffer: FfiBuffer | null = null;

  private disposed = false;

  constructor(pointer: Deno.PointerValue) {
    if (pointer === null) {
      throw new TypeError("Invalid pointer: cannot be null");
    }
    // Safe cast: null is ruled out above, so this is PointerObject
    this.pointer = pointer as Deno.PointerObject;
  }

  /**
   * Get error code (at offset 0)
   */
  get errorCode(): KrepisError {
    this.assertNotDisposed();
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    const code = this.view.getUint32(FfiResponse.OFFSET_ERROR_CODE);
    return code as KrepisError;
  }

  /**
   * Get result buffer (at offset 8)
   * Lazy-loads and caches the buffer
   */
  get resultBufferMut(): FfiBuffer {
    this.assertNotDisposed();
    if (!this.resultBuffer) {
      // Calculate pointer to embedded buffer structure
      const pointerVal = Deno.UnsafePointer.value(this.pointer);
      const bufferPtrVal = pointerVal + 8n;
      // Deno.UnsafePointer.create() returns PointerObject (non-null)
      const bufferPtr = Deno.UnsafePointer.create(bufferPtrVal);
      this.resultBuffer = new FfiBuffer(bufferPtr);
    }
    return this.resultBuffer;
  }

  /**
   * Check if response indicates success
   */
  isSuccess(): boolean {
    this.assertNotDisposed();
    return this.errorCode === KrepisError.Success;
  }

  /**
   * Check if response indicates error
   */
  isError(): boolean {
    this.assertNotDisposed();
    return this.errorCode !== KrepisError.Success;
  }

  /**
   * Get error message
   */
  getErrorMessage(): string {
    this.assertNotDisposed();
    return getKrepisErrorMessage(this.errorCode);
  }

  /**
   * Direct pointer access
   */
  getPointer(): Deno.PointerObject {
    this.assertNotDisposed();
    return this.pointer;
  }

  /**
   * Check if disposed
   */
  private assertNotDisposed(): void {
    if (this.disposed) {
      throw new ReferenceError("FfiResponse has been disposed");
    }
  }

  /**
   * Explicit disposal
   * Cleans up embedded result buffer
   */
  [Symbol.dispose](): void {
    if (this.disposed) return;
    this.disposed = true;
    this.view = null;

    if (this.resultBuffer) {
      this.resultBuffer[Symbol.dispose]();
      this.resultBuffer = null;
    }

    try {
      const lib = getKrepisLib();
      lib.symbols.free_buffer(this.pointer);
    } catch (error) {
      console.error("Failed to free FfiResponse:", error);
    }
  }
}

// ============================================================================
// 5. SHARED MEMORY METADATA
// ============================================================================

/**
 * SharedMemoryMetadata - Turbo-mode shared memory coordination
 *
 * Memory Layout (32 bytes, 8-byte aligned):
 * - Offset 0: version (u32, 4 bytes)
 * - Offset 4: lock_state (u32, 4 bytes)
 * - Offset 8: kernel_ts (u64, 8 bytes)
 * - Offset 16: sdk_ts (u64, 8 bytes)
 * - Offset 24: data_offset (u32, 4 bytes)
 * - Offset 28: data_size (u32, 4 bytes)
 */
export class SharedMemoryMetadata {
  private static readonly SIZE = 32;
  private static readonly ALIGN = 8;
  private static readonly OFFSET_VERSION = 0;
  private static readonly OFFSET_LOCK_STATE = 4;
  private static readonly OFFSET_KERNEL_TS = 8;
  private static readonly OFFSET_SDK_TS = 16;
  private static readonly OFFSET_DATA_OFFSET = 24;
  private static readonly OFFSET_DATA_SIZE = 28;

  // Lock state constants
  static readonly KERNEL_OWNED = 0;
  static readonly SDK_OWNED = 1;
  static readonly LOCKED = 2;

  /** Raw pointer to memory block (non-null PointerObject) */
  private pointer: Deno.PointerObject;

  private view: Deno.UnsafePointerView | null = null;
  private dataView: DataView | null = null;

  constructor(pointer: Deno.PointerValue) {
    if (pointer === null) {
      throw new TypeError("Invalid pointer: cannot be null");
    }
    // Safe cast: null is ruled out above, so this is PointerObject
    this.pointer = pointer as Deno.PointerObject;
  }

  /**
   * 쓰기 가능한 DataView를 지연 로딩(Lazy Loading)합니다.
   */
  private getWritableView(): DataView {
    if (!this.dataView) {
      if (!this.view) this.view = new Deno.UnsafePointerView(this.pointer);
      // SIZE(32바이트)만큼 네이티브 메모리를 참조하는 ArrayBuffer를 가져옵니다.
      const buffer = this.view.getArrayBuffer(SharedMemoryMetadata.SIZE);
      this.dataView = new DataView(buffer);
    }
    return this.dataView;
  }

  get version(): number {
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getUint32(SharedMemoryMetadata.OFFSET_VERSION);
  }

  get lockState(): number {
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getUint32(SharedMemoryMetadata.OFFSET_LOCK_STATE);
  }

  set lockState(value: number) {
    const v = this.getWritableView();
    // 두 번째 인자로 true를 전달하여 리틀 엔디안(Little-endian)을 명시합니다. (Rust와 일치)
    v.setUint32(SharedMemoryMetadata.OFFSET_LOCK_STATE, value, true);
  }

  get kernelTs(): bigint {
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getBigUint64(SharedMemoryMetadata.OFFSET_KERNEL_TS);
  }

  set kernelTs(value: bigint) {
    const v = this.getWritableView();
    v.setBigUint64(SharedMemoryMetadata.OFFSET_KERNEL_TS, value, true);
  }

  get sdkTs(): bigint {
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getBigUint64(SharedMemoryMetadata.OFFSET_SDK_TS);
  }

  set sdkTs(value: bigint) {
    const v = this.getWritableView();
    v.setBigUint64(SharedMemoryMetadata.OFFSET_SDK_TS, value, true);
  }

  get dataOffset(): number {
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getUint32(SharedMemoryMetadata.OFFSET_DATA_OFFSET);
  }

  get dataSize(): number {
    if (!this.view) {
      this.view = new Deno.UnsafePointerView(this.pointer);
    }
    return this.view.getUint32(SharedMemoryMetadata.OFFSET_DATA_SIZE);
  }

  isValid(): boolean {
    return this.dataOffset > 0 && this.dataSize > 0 && this.version > 0;
  }

  getPointer(): Deno.PointerObject {
    return this.pointer;
  }
}

// ============================================================================
// 6. SOVEREIGN CONTEXT INTERFACE
// ============================================================================

/**
 * IKrepisContext - TypeScript representation of SovereignContext
 *
 * Used for serialization/deserialization with kernel.
 * NOT an FFI struct (passed as JSON/binary blob).
 */
export interface IKrepisContext {
  /** Unique request identifier (UUID or snowflake) */
  requestId: string;

  /** Multi-tenant isolation scope */
  tenantId: string;

  /** Distributed trace correlation ID */
  traceId: string;

  /** Turbo-mode flag: true = shared memory FFI, false = standard FFI */
  isTurboMode: boolean;

  /** Request creation timestamp (Unix nanoseconds) */
  timestamp: bigint;
}

/**
 * Helper to create context from partial data
 */
export function createContext(
  requestId: string,
  tenantId: string,
  traceId: string,
  isTurboMode = false,
): IKrepisContext {
  return {
    requestId,
    tenantId,
    traceId,
    isTurboMode,
    timestamp: BigInt(Date.now()) * 1_000_000n, // ms to ns
  };
}

/**
 * Serialize context to JSON (for standard FFI)
 */
export function serializeContext(ctx: IKrepisContext): string {
  return JSON.stringify({
    request_id: ctx.requestId,
    tenant_id: ctx.tenantId,
    trace_id: ctx.traceId,
    is_turbo_mode: ctx.isTurboMode,
    timestamp: ctx.timestamp.toString(),
  });
}

/**
 * Deserialize context from JSON
 */
export function deserializeContext(json: string): IKrepisContext {
  const obj = JSON.parse(json) as Record<string, unknown>;
  return {
    requestId: String(obj.request_id ?? ""),
    tenantId: String(obj.tenant_id ?? ""),
    traceId: String(obj.trace_id ?? ""),
    isTurboMode: Boolean(obj.is_turbo_mode),
    timestamp: BigInt(String(obj.timestamp ?? "0")),
  };
}

// ============================================================================
// 7. EXPORT SUMMARY
// ============================================================================

export const VERSION = "0.1.0";
export const FFI_ABI_VERSION = (1 << 16) | 1; // 1.1.0 packed as u32