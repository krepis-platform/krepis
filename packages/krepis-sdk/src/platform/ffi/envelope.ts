/**
 * @file envelope.ts
 * @version 1.0.0
 * @spec [Spec-Dev-002] Sovereign Bridge v1.1.0
 * 
 * FfiResponse Protobuf Envelope를 디코딩하고 성공/실패를 처리합니다.
 * 커널의 모든 응답은 이 레이어를 통과하여 타입-안전한 TS 객체로 변환됩니다.
 */

import protobuf from "npm:protobufjs@^7.2.5";
import {
  type FfiResponse,
  type KrepisError,
  ErrorCode,
  ErrorCategory,
  readFfiBuffer,
  createBufferGuard,
  ResourceSnapshot,
} from "./layout.ts";
import type { KernelSymbols } from "./loader.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Protobuf Schema Initialization
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

const Root = protobuf.Root || (protobuf as any).default?.Root;
if (!Root) {
  throw new Error("[FFI Envelope] Failed to load protobuf.Root. Check protobufjs installation.");
}
/**
 * Protobuf 스키마를 런타임에 정의합니다.
 * 
 * 참조: proto/error.proto, proto/context.proto
 * 
 * 이상적으로는 protobuf.js의 pbjs를 통해 사전 컴파일된 .js 파일을 사용해야 하지만,
 * 초기 구현에서는 런타임 정의를 사용합니다.
 */
const root = Root.fromJSON({
  nested: {
    krepis: {
      nested: {
        core: {
          nested: {
            // ErrorCode enum
            ErrorCode: {
              values: {
                ERROR_CODE_UNKNOWN: 0,
                ERROR_CODE_TENANT_INACTIVE: 1,
                ERROR_CODE_TENANT_NOT_FOUND: 2,
                ERROR_CODE_QUOTA_EXCEEDED: 10,
                ERROR_CODE_ACQUIRE_TIMEOUT: 11,
                ERROR_CODE_EXECUTION_TIMEOUT: 12,
                ERROR_CODE_MEMORY_LIMIT_EXCEEDED: 13,
                ERROR_CODE_PATH_DENIED: 20,
                ERROR_CODE_PERMISSION_DENIED: 21,
                ERROR_CODE_INTERNAL: 90,
                ERROR_CODE_SERIALIZATION_FAILED: 91,
                ERROR_CODE_RUNTIME_PANIC: 92,
              },
            },
            // ErrorCategory enum
            ErrorCategory: {
              values: {
                ERROR_CATEGORY_UNKNOWN: 0,
                ERROR_CATEGORY_TRANSIENT: 1,
                ERROR_CATEGORY_THROTTLING: 2,
                ERROR_CATEGORY_CLIENT: 3,
                ERROR_CATEGORY_SERVER: 4,
                ERROR_CATEGORY_TIMEOUT: 5,
              },
            },
            // ResourceSnapshot message
            ResourceSnapshot: {
              fields: {
                currentConcurrent: { type: "uint32", id: 1 },
                maxConcurrent: { type: "uint32", id: 2 },
                heapUsedBytes: { type: "uint64", id: 3 },
                heapLimitBytes: { type: "uint64", id: 4 },
                elapsedMs: { type: "uint64", id: 5 },
                limitMs: { type: "uint64", id: 6 },
              },
            },
            // ErrorMeta message
            ErrorMeta: {
              fields: {
                retryable: { type: "bool", id: 1 },
                category: { type: "ErrorCategory", id: 2 },
                retryAfterMs: { type: "uint64", id: 3 },
                attempt: { type: "uint32", id: 4 },
                maxAttempts: { type: "uint32", id: 5 },
                resourceSnapshot: { type: "ResourceSnapshot", id: 10 },
                //extensions: { keyType: "string", type: "string", id: 15 },
              },
            },
            // KrepisError message
            KrepisError: {
              fields: {
                code: { type: "ErrorCode", id: 1 },
                message: { type: "string", id: 2 },
                meta: { type: "ErrorMeta", id: 3 },
                tenantId: { type: "string", id: 10 },
                requestId: { type: "string", id: 11 },
                traceId: { type: "string", id: 12 },
                timestamp: { type: "int64", id: 13 },
                stackTrace: { type: "string", id: 20 },
                source: { type: "string", id: 21 },
              },
            },
            // FfiResponse message
            FfiResponse: {
              oneofs: {
                result: {
                  oneof: ["successPayload", "error"],
                },
              },
              fields: {
                successPayload: { type: "bytes", id: 1 },
                error: { type: "KrepisError", id: 2 },
                requestId: { type: "string", id: 10 },
                traceId: { type: "string", id: 11 },
                durationUs: { type: "uint64", id: 12 },
                protocolVersion: { type: "uint32", id: 15 },
              },
            },
          },
        },
      },
    },
  },
});

const FfiResponseProto = root.lookupType("krepis.core.FfiResponse");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Domain Error Class
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Krepis 커널 에러를 나타내는 도메인 에러 클래스.
 * 
 * Protobuf의 KrepisError를 TS Error 객체로 변환하여 표준 에러 처리 패턴을 지원합니다.
 */
export class KrepisBridgeError extends Error {
  public readonly code: ErrorCode;
  public readonly category: ErrorCategory;
  public readonly tenantId: string;
  public readonly requestId: string;
  public readonly traceId: string;
  public readonly timestamp: Date;
  public readonly retryable: boolean;
  public readonly retryAfterMs: number;
  public readonly resourceSnapshot?: ResourceSnapshot;

  constructor(error: KrepisError) {
    super(error.message);
    this.name = "KrepisBridgeError";
    this.code = error.code;
    this.category = error.meta?.category ?? ErrorCategory.ERROR_CATEGORY_UNKNOWN;
    this.tenantId = error.tenantId;
    this.requestId = error.requestId;
    this.traceId = error.traceId;
    this.timestamp = new Date(Number(error.timestamp));
    this.retryable = error.meta?.retryable ?? false;
    this.retryAfterMs = error.meta?.retryAfterMs ? Number(error.meta.retryAfterMs) : 0;
    this.resourceSnapshot = error.meta?.resourceSnapshot;

    Object.setPrototypeOf(this, KrepisBridgeError.prototype);

    // 스택 트레이스가 있으면 포함
    if (error.stackTrace) {
      this.stack = `${this.stack}\n\nKernel Stack Trace:\n${error.stackTrace}`;
    }

    // Error.captureStackTrace 지원 환경에서 스택 정리
    if (Error.captureStackTrace) {
      Error.captureStackTrace(this, KrepisBridgeError);
    }
  }

  /**
   * 에러 정보를 구조화된 객체로 반환합니다.
   * 로깅 및 디버깅에 유용합니다.
   */
  toJSON() {
    return {
      name: this.name,
      code: ErrorCode[this.code],
      category: ErrorCategory[this.category],
      message: this.message,
      tenantId: this.tenantId,
      requestId: this.requestId,
      traceId: this.traceId,
      timestamp: this.timestamp.toISOString(),
      retryable: this.retryable,
      retryAfterMs: this.retryAfterMs,
      resourceSnapshot: this.resourceSnapshot,
    };
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Unwrap Functions
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * FfiBuffer 포인터에서 FfiResponse를 디코딩합니다.
 * 
 * @param bufferPtr - Rust에서 반환된 *mut FfiBuffer 포인터
 * @returns 디코딩된 FfiResponse 객체
 * @throws {Error} Protobuf 디코딩 실패 시
 * 
 * @internal 일반적으로 직접 호출하지 않고 unwrapFfiResponse를 사용합니다.
 */
function decodeFfiResponse(bufferPtr: Deno.PointerValue): FfiResponse {
  const payload = readFfiBuffer(bufferPtr);
  
  try {
    const message = FfiResponseProto.decode(payload);
    const obj = FfiResponseProto.toObject(message, {
      longs: Number, // int64를 number로 변환 (JS의 제한)
      enums: Number, // enum을 숫자로 변환
      bytes: Array,  // bytes를 Uint8Array로 유지
      defaults: false,
    });

    // oneof result를 타입-안전한 형태로 변환
    const result = obj.error
      ? { type: "error" as const, error: obj.error as KrepisError }
      : { type: "success" as const, payload: new Uint8Array(obj.successPayload || []) };

    return {
      result,
      requestId: obj.requestId || "",
      traceId: obj.traceId || "",
      durationUs: BigInt(obj.durationUs || 0),
      protocolVersion: obj.protocolVersion || 1,
    };
  } catch (err) {
    throw new Error(
      `[FFI Envelope] Failed to decode FfiResponse: ${
        err instanceof Error ? err.message : String(err)
      }`
    );
  }
}

/**
 * FfiBuffer를 unwrap하여 성공 페이로드를 반환하거나 에러를 throw합니다.
 * 
 * 이 함수는 Explicit Resource Management를 사용하여 메모리를 자동 해제합니다.
 * 
 * @param bufferPtr - Rust에서 반환된 *mut FfiBuffer 포인터
 * @param freeBufferFn - 커널의 free_buffer FFI 함수
 * @returns 성공 시 페이로드 Uint8Array
 * @throws {KrepisBridgeError} 커널 에러 발생 시
 * @throws {Error} Protobuf 디코딩 실패 시
 * 
 * @example
 * ```ts
 * const kernel = loadKernelFFI();
 * const bufferPtr = kernel.symbols.create_context(...);
 * 
 * try {
 *   const payload = unwrapFfiResponse(bufferPtr, kernel.symbols.free_buffer);
 *   const context = KrepisContext.decode(payload);
 * } catch (err) {
 *   if (err instanceof KrepisBridgeError) {
 *     console.error("Kernel error:", err.toJSON());
 *   }
 *   throw err;
 * }
 * ```
 */
export function unwrapFfiResponse(
  bufferPtr: Deno.PointerValue,
  freeBufferFn: KernelSymbols["free_buffer"]
): Uint8Array {
  using _guard = createBufferGuard(bufferPtr, freeBufferFn);
  const response = decodeFfiResponse(bufferPtr);

  if (response.result.type === "success") {
    return response.result.payload;
  }
  
  // 에러 발생 시
  throw new KrepisBridgeError(response.result.error);
}

/**
 * unwrapFfiResponse의 비동기 버전.
 * 
 * 현재는 단순히 동기 버전을 래핑하지만, 향후 비동기 디코딩이나
 * 추가 처리 로직을 위한 확장 지점으로 남겨둡니다.
 * 
 * @param bufferPtr - Rust에서 반환된 *mut FfiBuffer 포인터
 * @param freeBufferFn - 커널의 free_buffer FFI 함수
 * @returns Promise<성공 페이로드>
 */
export async function unwrapFfiResponseAsync(
  bufferPtr: Deno.PointerValue,
  freeBufferFn: KernelSymbols["free_buffer"]
): Promise<Uint8Array> {
  return await unwrapFfiResponse(bufferPtr, freeBufferFn);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4] Specialized Unwrappers (Type-Safe Helpers)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * FfiResponse를 디코딩하되 에러를 throw하지 않고 Result 타입으로 반환합니다.
 * 
 * 함수형 프로그래밍 스타일에서 유용합니다.
 * 
 * @param bufferPtr - Rust에서 반환된 *mut FfiBuffer 포인터
 * @param freeBufferFn - 커널의 free_buffer FFI 함수
 * @returns Result<Uint8Array, KrepisBridgeError>
 */
export function unwrapFfiResponseResult(
  bufferPtr: Deno.PointerValue,
  freeBufferFn: KernelSymbols["free_buffer"]
): { ok: true; value: Uint8Array } | { ok: false; error: KrepisBridgeError } {
  try {
    const payload = unwrapFfiResponse(bufferPtr, freeBufferFn);
    return { ok: true, value: payload };
  } catch (err) {
    if (err instanceof KrepisBridgeError) {
      return { ok: false, error: err };
    }
    // Protobuf 디코딩 에러 등은 재throw
    throw err;
  }
}

/**
 * 원시(raw) FfiResponse 객체를 반환합니다.
 * 
 * 디버깅이나 로깅 목적으로 사용하며, 일반적으로는 unwrapFfiResponse를 사용하는 것이 좋습니다.
 * 
 * @param bufferPtr - Rust에서 반환된 *mut FfiBuffer 포인터
 * @param freeBufferFn - 커널의 free_buffer FFI 함수
 * @returns 디코딩된 FfiResponse 객체
 */
export function getRawFfiResponse(
  bufferPtr: Deno.PointerValue,
  freeBufferFn: KernelSymbols["free_buffer"]
): FfiResponse {
  using _guard = createBufferGuard(bufferPtr, freeBufferFn);
  return decodeFfiResponse(bufferPtr);
}