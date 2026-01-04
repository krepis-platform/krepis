/**
 * @module @krepis/sdk
 * @version 0.1.0
 * 
 * Krepis Sovereign SDK - TypeScript/Deno Edition
 * 
 * This is the main entry point for the Krepis SDK. It provides a high-level
 * interface to interact with the Krepis Sovereign Kernel.
 * 
 * @example
 * ```typescript
 * import { KrepisClient } from "@krepis/sdk";
 * 
 * const client = new KrepisClient();
 * await client.initialize();
 * ```
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Platform Layer] - Raw FFI Bridge
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

export {
  // FFI Loader
  loadKernelFFI,
  unloadKernelFFI,
  getKernel,
  type KernelFFI,
  type KernelSymbols,
  
  // Layout & Types
  ErrorCode,
  ErrorCategory,
  type KrepisError,
  type FfiResponse,
  type ResourceSnapshot,
  type ErrorMeta,
  
  // Unwrapping
  unwrapFfiResponse,
  unwrapFfiResponseAsync,
  unwrapFfiResponseResult,
  KrepisBridgeError,
  
  // Helpers
  readFfiBuffer,
  createBufferGuard,
  isSuccessResponse,
  isErrorResponse,
  isRetryableError,
  getDefaultRetryDelay,
} from "./src/platform/ffi/mod.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Core Layer] - Context & DI (Task 2 ✅)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Context Module
export {
  type IKrepisContext,
  type ContextOptions,
  type ContextValidation,
  ContextState,
  ContextValidator,
  ContextFactory,
  createContext,
  createContextFromRequest,
  isKrepisContext,
  isDisposed,
} from "./src/core/context/mod.ts";

// DI Module
export {
  InjectionToken,
  type ServiceIdentifier,
  type Constructor,
  type ServiceDescriptor,
  ServiceLifetime,
  type IScopedContainer,
  type IServiceProvider,
  type IServiceCollection,
  type ILogger,
  type ITelemetry,
  KREPIS_CONTEXT,
  LOGGER,
  TELEMETRY,
  createServiceCollection,
} from "./src/core/di/mod.ts";

// TODO(@sukryu): Export Pipeline, Middleware (Task 3)

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Client Layer] - High-Level API (Coming in Task 3+)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// TODO(@sukryu): Export KrepisClient

/**
 * SDK 버전 정보
 */
export const VERSION = "0.1.0";

/**
 * Trinity 아키텍처 버전
 */
export const TRINITY_VERSION = "1.0.0";