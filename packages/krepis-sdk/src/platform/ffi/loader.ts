/**
 * @file loader.ts
 * @version 1.0.0
 * @spec [Spec-Dev-002] Sovereign Bridge v1.1.0
 * 
 * OS별 커널 바이너리를 동적으로 로드하고 FFI 심볼을 바인딩합니다.
 * 바이너리는 packages/krepis-sdk/bin/{os}-{arch}/ 디렉토리에 위치합니다.
 */

import { fromFileUrl, join, dirname } from "https://deno.land/std/path/mod.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Platform Detection
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 지원 플랫폼 목록.
 * Cargo 빌드 타겟과 일치해야 합니다.
 */
export type SupportedPlatform =
  | "linux-x86_64"
  | "linux-aarch64"
  | "darwin-x86_64"
  | "darwin-aarch64"
  | "windows-x86_64";

/**
 * 현재 실행 환경의 플랫폼을 감지합니다.
 * 
 * @returns 플랫폼 식별자 (예: "darwin-aarch64")
 * @throws {Error} 지원하지 않는 플랫폼인 경우
 */
function detectPlatform(): SupportedPlatform {
  const os = Deno.build.os;
  const arch = Deno.build.arch;

  const platformMap: Record<string, SupportedPlatform> = {
    "linux-x86_64": "linux-x86_64",
    "linux-aarch64": "linux-aarch64",
    "darwin-x86_64": "darwin-x86_64",
    "darwin-aarch64": "darwin-aarch64",
    "windows-x86_64": "windows-x86_64",
  };

  const key = `${os}-${arch}`;
  const platform = platformMap[key];

  if (!platform) {
    throw new Error(
      `[FFI Loader] Unsupported platform: ${os}-${arch}. ` +
      `Supported platforms: ${Object.keys(platformMap).join(", ")}`
    );
  }

  return platform;
}

/**
 * 플랫폼별 바이너리 파일명을 반환합니다.
 * 
 * @param platform - 플랫폼 식별자
 * @returns 바이너리 파일명 (예: "libkrepis_kernel.dylib")
 */
function getBinaryName(platform: SupportedPlatform): string {
  if (platform.startsWith("windows")) {
    return "krepis_kernel.dll";
  } else if (platform.startsWith("darwin")) {
    return "libkrepis_kernel.dylib";
  } else {
    return "libkrepis_kernel.so";
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] FFI Symbol Definitions
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Rust 커널이 익스포트하는 FFI 함수 시그니처.
 * 
 * 참조: crates/krepis-kernel/src/ffi/bridge.rs
 * 
 * ```rust
 * #[no_mangle]
 * pub extern "C" fn initialize_kernel(buffer_ptr: *const u8, buffer_len: usize) -> *mut FfiBuffer;
 * 
 * #[no_mangle]
 * pub extern "C" fn create_context(
 *     request_id_ptr: *const u8,
 *     request_id_len: usize,
 *     is_turbo: bool
 * ) -> *mut FfiBuffer;
 * 
 * #[no_mangle]
 * pub extern "C" fn free_buffer(ptr: *mut FfiBuffer);
 * ```
 */
const kernelSymbols = {
  /**
   * 커널 초기화.
   * InitializeRequest Protobuf를 전달하여 시스템을 부팅합니다.
   * 
   * @param buffer_ptr - Protobuf 직렬화된 InitializeRequest 포인터
   * @param buffer_len - 버퍼 길이
   * @returns FfiBuffer 포인터 (FfiResponse Envelope 포함)
   */
  initialize_kernel: {
    parameters: ["buffer", "usize"],
    result: "pointer",
  } as const,

  /**
   * 새로운 KrepisContext 생성.
   * 
   * @param request_id_ptr - Request ID 문자열 포인터
   * @param request_id_len - Request ID 길이
   * @param is_turbo - Turbo 모드 활성화 여부
   * @returns FfiBuffer 포인터 (KrepisContext Protobuf 포함)
   */
  create_context: {
    parameters: ["buffer", "usize"],
    result: "pointer",
  } as const,

  /**
   * FfiBuffer 메모리 해제.
   * Rust의 Box::from_raw를 통해 메모리를 회수합니다.
   * 
   * @param ptr - 해제할 FfiBuffer 포인터
   */
  free_buffer: {
    parameters: ["pointer"],
    result: "void",
  } as const,
} as const;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Loader Implementation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 로드된 커널 FFI 라이브러리 핸들.
 */
export type KernelFFI = Deno.DynamicLibrary<typeof kernelSymbols>;

/**
 * 전역 싱글톤 인스턴스.
 * 동일 프로세스 내에서 라이브러리는 한 번만 로드됩니다.
 */
let cachedKernel: KernelFFI | null = null;

/**
 * Krepis 커널 바이너리를 로드하고 FFI 심볼을 바인딩합니다.
 * 
 * @param options - 로드 옵션
 * @param options.binDir - 바이너리 디렉토리 경로 (기본값: auto-detect)
 * @param options.reload - 기존 캐시를 무시하고 강제 재로드
 * @returns FFI 라이브러리 핸들
 * 
 * @throws {Error} 바이너리를 찾을 수 없거나 로드에 실패한 경우
 * 
 * @example
 * ```ts
 * const kernel = loadKernelFFI();
 * const bufferPtr = kernel.symbols.create_context(...);
 * ```
 */
export function loadKernelFFI(options?: {
  binDir?: string;
  reload?: boolean;
}): KernelFFI {
  // 캐시된 인스턴스 반환
  if (cachedKernel && !options?.reload) {
    return cachedKernel;
  }

  const platform = detectPlatform();
  const binaryName = getBinaryName(platform);

  // 바이너리 경로 결정
  let binaryPath: string;
  if (options?.binDir) {
    // 사용자 지정 경로
    binaryPath = `${options.binDir}/${binaryName}`;
  } else {
    const currentDir = dirname(fromFileUrl(import.meta.url));
    const sdkRoot = join(currentDir, "../../.."); 
    binaryPath = join(sdkRoot, "bin", platform, binaryName);
  }

  // 바이너리 존재 여부 확인
  try {
    Deno.statSync(binaryPath);
  } catch (err) {
    if (err instanceof Deno.errors.NotFound) {
      throw new Error(`[FFI Loader] Kernel binary not found at: ${binaryPath}`);
    }
    throw err;
  }

  // FFI 라이브러리 로드
  try {
    return cachedKernel = Deno.dlopen(binaryPath, kernelSymbols);
  } catch (err) {
    throw new Error(`[FFI Loader] Failed to load kernel: ${binaryPath}\n${err}`);
  }
}

/**
 * 로드된 커널 라이브러리를 명시적으로 언로드합니다.
 * 
 * ⚠️ 주의: 언로드 후 기존 포인터를 사용하면 Segmentation Fault가 발생할 수 있습니다.
 * 일반적으로 프로세스 종료 시 자동으로 해제되므로 명시적 호출은 불필요합니다.
 */
export function unloadKernelFFI(): void {
  if (cachedKernel) {
    cachedKernel.close();
    cachedKernel = null;
    console.log("[FFI Loader] Kernel unloaded");
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4] Convenience Exports
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 기본 커널 인스턴스를 가져옵니다.
 * 첫 호출 시 자동으로 로드됩니다.
 */
export function getKernel(): KernelFFI {
  return loadKernelFFI();
}

/**
 * Type-safe 심볼 접근을 위한 타입 정의.
 */
export type KernelSymbols = KernelFFI["symbols"];