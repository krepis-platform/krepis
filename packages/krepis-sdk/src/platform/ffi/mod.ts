/**
 * @file mod.ts
 * @version 1.0.0
 * 
 * FFI 플랫폼 레이어의 통합 진입점.
 * 외부 모듈은 이 파일을 통해 Raw FFI Bridge에 접근합니다.
 */

// Layout & Type Definitions
export {
  FfiBufferLayout,
  ErrorCode,
  ErrorCategory,
  type ResourceSnapshot,
  type ErrorMeta,
  type KrepisError,
  type FfiResponse,
  readFfiBuffer,
  createBufferGuard,
  isSuccessResponse,
  isErrorResponse,
  isRetryableError,
  getDefaultRetryDelay,
} from "./layout.ts";

// Dynamic Library Loader
export {
  type KernelFFI,
  type KernelSymbols,
  type SupportedPlatform,
  loadKernelFFI,
  unloadKernelFFI,
  getKernel,
} from "./loader.ts";

// Envelope Unwrapping & Error Handling
export {
  KrepisBridgeError,
  unwrapFfiResponse,
  unwrapFfiResponseAsync,
  unwrapFfiResponseResult,
  getRawFfiResponse,
} from "./envelope.ts";