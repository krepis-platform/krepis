/**
 * @file layout.ts
 * @version 1.0.0
 * @spec [Spec-Dev-002] Sovereign Bridge v1.1.0
 * @spec [Spec-Dev-001] Memory Safety v1.6.0
 * 
 * Rust 커널의 FfiBuffer 구조를 8바이트 정렬 규격에 따라 TS에서 미러링합니다.
 * 이 파일은 Zero-copy 메모리 전달의 기초가 되며, 한 치의 오차도 허용되지 않습니다.
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] FfiBuffer Layout - Rust #[repr(C, align(8))] 미러링
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Rust의 FfiBuffer 구조체와 정확히 일치하는 메모리 레이아웃.
 * 
 * Rust:
 * ```rust
 * #[repr(C, align(8))]
 * pub struct FfiBuffer {
 *     pub data: *mut u8,      // 0-7
 *     pub len: usize,         // 8-15
 *     pub cap: usize,         // 16-23
 *     pub _padding: u64,      // 24-31 (ABI 안정성)
 * }
 * ```
 * 
 * 총 32바이트로 구성되며, 모든 필드는 8바이트 경계에 정렬됩니다.
 */
export const FfiBufferLayout = {
  struct: [
    "pointer",  // data: *mut u8 (8 bytes on 64-bit)
    "usize",    // len: usize (8 bytes)
    "usize",    // cap: usize (8 bytes)
    "u64",      // _padding: u64 (8 bytes)
  ] as const,
  
  /** 구조체 총 크기 (바이트) */
  SIZE: 32,
  
  /** 각 필드의 오프셋 (바이트) */
  OFFSET: {
    DATA: 0,
    LEN: 8,
    CAP: 16,
    PADDING: 24,
  } as const,
} as const;

/**
 * FfiBuffer 포인터에서 실제 데이터를 추출하는 헬퍼 함수.
 * 
 * @param bufferPtr - Rust에서 반환된 *mut FfiBuffer 포인터
 * @returns 데이터 영역의 Uint8Array 뷰
 * 
 * @throws {Error} NULL 포인터 전달 시
 * 
 * @example
 * ```ts
 * const bufferPtr = kernel.create_context(...);
 * const data = readFfiBuffer(bufferPtr);
 * console.log(data.length); // 실제 데이터 길이
 * ```
 */
export function readFfiBuffer(bufferPtr: Deno.PointerValue): Uint8Array {
  if (!bufferPtr) {
    throw new Error("[FFI Layout] Cannot read from NULL FfiBuffer pointer");
  }

  // 1. FfiBuffer 구조체를 DataView로 읽기
  const bufferView = new Deno.UnsafePointerView(bufferPtr);
  const structBytes = new Uint8Array(FfiBufferLayout.SIZE);
  bufferView.copyInto(structBytes, 0);
  const dataView = new DataView(structBytes.buffer);

  // 2. 필드 값 추출 (Little-Endian, 64-bit 가정)
  // bigint를 명시적인 Deno.PointerValue로 변환해야 합니다.
  const rawDataPtr = dataView.getBigUint64(FfiBufferLayout.OFFSET.DATA, true);
  const dataPtr = Deno.UnsafePointer.create(rawDataPtr); // ✨ 캐스팅 추가
  
  const len = Number(dataView.getBigUint64(FfiBufferLayout.OFFSET.LEN, true));

  if (!dataPtr) {
    // 내부 data 포인터가 NULL인 경우 처리
    return new Uint8Array(0);
  }

  // 3. 실제 데이터 영역을 Uint8Array로 매핑
  const dataView2 = new Deno.UnsafePointerView(dataPtr);
  const payload = new Uint8Array(len);
  dataView2.copyInto(payload, 0);

  return payload;
}

/**
 * FfiBuffer를 안전하게 해제하는 래퍼.
 * Explicit Resource Management와 함께 사용됩니다.
 * 
 * @param ptr - 해제할 FfiBuffer 포인터
 * @param freeBufferFn - 커널의 free_buffer FFI 함수
 * 
 * @example
 * ```ts
 * const bufferPtr = kernel.create_context(...);
 * using _ = createBufferGuard(bufferPtr, kernel.symbols.free_buffer);
 * // 블록 종료 시 자동 해제
 * ```
 */
export function createBufferGuard(
  ptr: Deno.PointerValue,
  freeBufferFn: (ptr: Deno.PointerValue) => void
): Disposable {
  return {
    [Symbol.dispose]() {
      if (ptr !== null) {
        freeBufferFn(ptr);
      }
    },
  };
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Protobuf Message Type Mappings
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * proto/error.proto의 ErrorCode 열거형 미러링.
 * Rust와 동일한 정수 값을 사용합니다.
 */
export enum ErrorCode {
  ERROR_CODE_UNKNOWN = 0,
  ERROR_CODE_TENANT_INACTIVE = 1,
  ERROR_CODE_TENANT_NOT_FOUND = 2,
  ERROR_CODE_QUOTA_EXCEEDED = 10,
  ERROR_CODE_ACQUIRE_TIMEOUT = 11,
  ERROR_CODE_EXECUTION_TIMEOUT = 12,
  ERROR_CODE_MEMORY_LIMIT_EXCEEDED = 13,
  ERROR_CODE_PATH_DENIED = 20,
  ERROR_CODE_PERMISSION_DENIED = 21,
  ERROR_CODE_INTERNAL = 90,
  ERROR_CODE_SERIALIZATION_FAILED = 91,
  ERROR_CODE_RUNTIME_PANIC = 92,
}

/**
 * proto/error.proto의 ErrorCategory 열거형 미러링.
 */
export enum ErrorCategory {
  ERROR_CATEGORY_UNKNOWN = 0,
  ERROR_CATEGORY_TRANSIENT = 1,
  ERROR_CATEGORY_THROTTLING = 2,
  ERROR_CATEGORY_CLIENT = 3,
  ERROR_CATEGORY_SERVER = 4,
  ERROR_CATEGORY_TIMEOUT = 5,
}

/**
 * ResourceSnapshot - 에러 발생 시점의 리소스 상태 스냅샷.
 */
export interface ResourceSnapshot {
  currentConcurrent: number;
  maxConcurrent: number;
  heapUsedBytes: bigint;
  heapLimitBytes: bigint;
  elapsedMs: bigint;
  limitMs: bigint;
}

/**
 * ErrorMeta - 에러 메타데이터 (재시도 정책, 카테고리 등).
 */
export interface ErrorMeta {
  retryable: boolean;
  category: ErrorCategory;
  retryAfterMs: bigint;
  attempt: number;
  maxAttempts: number;
  resourceSnapshot?: ResourceSnapshot;
  extensions: Record<string, string>;
}

/**
 * KrepisError - 커널에서 반환하는 표준 에러 구조.
 * FfiResponse.error 필드에 담깁니다.
 */
export interface KrepisError {
  code: ErrorCode;
  message: string;
  meta?: ErrorMeta;
  tenantId: string;
  requestId: string;
  traceId: string;
  timestamp: bigint;
  stackTrace?: string;
  source?: string;
}

/**
 * FfiResponse - 모든 FFI 호출의 통합 응답 envelope.
 * oneof result { success_payload, error } 구조를 TS로 표현.
 */
export interface FfiResponse {
  result:
    | { type: "success"; payload: Uint8Array }
    | { type: "error"; error: KrepisError };
  requestId: string;
  traceId: string;
  durationUs: bigint;
  protocolVersion: number;
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Type Guards & Validation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * FfiResponse의 성공 여부를 타입-안전하게 체크합니다.
 */
export function isSuccessResponse(
  response: FfiResponse
): response is FfiResponse & { result: { type: "success"; payload: Uint8Array } } {
  return response.result.type === "success";
}

/**
 * FfiResponse의 에러 여부를 타입-안전하게 체크합니다.
 */
export function isErrorResponse(
  response: FfiResponse
): response is FfiResponse & { result: { type: "error"; error: KrepisError } } {
  return response.result.type === "error";
}

/**
 * 에러가 재시도 가능한지 판단합니다.
 */
export function isRetryableError(error: KrepisError): boolean {
  return error.meta?.retryable ?? false;
}

/**
 * 에러 카테고리에 따른 기본 재시도 지연 시간(ms)을 계산합니다.
 */
export function getDefaultRetryDelay(error: KrepisError): number {
  if (error.meta?.retryAfterMs) {
    return Number(error.meta.retryAfterMs);
  }

  switch (error.meta?.category) {
    case ErrorCategory.ERROR_CATEGORY_THROTTLING:
      return 500;
    case ErrorCategory.ERROR_CATEGORY_TRANSIENT:
      return 100;
    case ErrorCategory.ERROR_CATEGORY_TIMEOUT:
      return 1000;
    default:
      return 0; // 재시도 불가
  }
}