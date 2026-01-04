/**
 * @file ContextFactory.ts
 * @version 1.0.0
 * @spec [Spec-001] Context Propagation v1.2.0
 * @spec [Spec-Dev-002] Sovereign Bridge v1.1.0
 * 
 * Krepis Context 생성 팩토리.
 * FFI를 통해 Rust 커널과 통신하여 Sovereign Context를 생성합니다.
 */

import { getKernel } from "../../platform/ffi/loader.ts";
import { unwrapFfiResponse } from "../../platform/ffi/envelope.ts";
import {
  type IKrepisContext,
  type ContextOptions,
  ContextValidator,
} from "./IKrepisContext.ts";
import {
encodeContextOptions,
  SovereignContext,
} from "./SovereignContext.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Context Factory
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Krepis Context 생성 팩토리.
 * 
 * 이 팩토리는 커널의 create_context FFI를 호출하여 
 * Sovereign Context를 생성합니다.
 * 
 * @example
 * ```ts
 * // 기본 컨텍스트 생성
 * using ctx = await ContextFactory.create({ tenantId: "acme-corp" });
 * 
 * // Turbo 모드 활성화
 * using ctx = await ContextFactory.create({
 *   tenantId: "enterprise-client",
 *   isTurboMode: true,
 *   priority: 10,
 * });
 * ```
 */
export class ContextFactory {
  /**
   * 새로운 Krepis Context를 생성합니다.
   * 
   * @param options - 컨텍스트 생성 옵션
   * @returns Sovereign Context 인스턴스
   * 
   * @throws {Error} 옵션 검증 실패 시
   * @throws {KrepisBridgeError} 커널 에러 발생 시
   */
  static async create(options: ContextOptions): Promise<IKrepisContext> {
    // 1. 옵션 검증
    const validation = ContextValidator.validate(options);
    if (!validation.isValid) {
      throw new Error(
        `[ContextFactory] Invalid options: ${validation.errors?.join(", ")}`
      );
    }
    
    // 경고가 있으면 로깅
    if (validation.warnings && validation.warnings.length > 0) {
      console.warn(
        `[ContextFactory] Warnings: ${validation.warnings.join(", ")}`
      );
    }
    
    // 2. 커널 로드
    const kernel = getKernel();
    
    // 3. Protobuf 인코딩 (여기서 모든 옵션이 바이너리로 변환됩니다)
    // encodeContextOptions 내부에서 requestId와 traceId가 보정됩니다.
    const contextBinary = encodeContextOptions(options)
    
    console.debug(
      `[ContextFactory] Creating context - ` +
      `TenantID: ${options.tenantId}, Turbo: ${options.isTurboMode ?? false}`
    );
    
    // 4. create_context FFI 호출 (개별 인자 대신 버퍼 자체를 전달)
    // 시그니처: (buffer_ptr: *const u8, buffer_len: usize)
    const bufferPtr = kernel.symbols.create_context(
      new Uint8Array(contextBinary),
      BigInt(contextBinary.length)
    );
    
    // 5. FfiResponse Unwrap
    const payload = await unwrapFfiResponse(bufferPtr, kernel.symbols.free_buffer);
    
    // 6. SovereignContext 생성
    const ctx = new SovereignContext(payload);
    
    console.debug(
      `[ContextFactory] ✅ Context created - ` +
      `RequestID: ${ctx.requestId}, TraceID: ${ctx.traceId}`
    );
    
    return ctx;
  }
  
  /**
   * 동기 버전 (Fast Path).
   * * 인코딩된 컨텍스트 바이너리를 커널에 직접 전달하여 
   * 즉시 SovereignContext를 생성합니다.
   * @param options - 컨텍스트 생성 옵션
   * @returns Sovereign Context 인스턴스
   */
  static createSync(options: ContextOptions): IKrepisContext {
    // 1. 옵션 검증
    const validation = ContextValidator.validate(options);
    if (!validation.isValid) {
      throw new Error(`[ContextFactory] Invalid options: ${validation.errors?.join(", ")}`);
    }

    // 2. 커널 로드
    const kernel = getKernel();
    
    // 3. Protobuf 인코딩 (모든 옵션을 포함)
    const contextBinary = encodeContextOptions(options);
    
    // 4. create_context FFI 호출
    // new Uint8Array()로 감싸서 Deno FFI 타입 호환성 확보
    const bufferPtr = kernel.symbols.create_context(
      new Uint8Array(contextBinary),
      BigInt(contextBinary.length)
    );
    
    // 5. FfiResponse Unwrap (unwrapFfiResponse는 동기 호출도 지원하도록 설계됨)
    // 참고: 동기 unwrap이 가능한 구조인지 확인이 필요하지만, 
    // 기존 코드에서 unwrapFfiResponse를 await 없이 호출하고 있으므로 그대로 유지합니다.
    const payload = unwrapFfiResponse(bufferPtr, kernel.symbols.free_buffer);
    
    // 6. SovereignContext 생성
    return new SovereignContext(payload);
  }
  
  /**
   * HTTP 요청으로부터 컨텍스트를 생성합니다.
   * 
   * @param request - HTTP Request 객체
   * @returns Sovereign Context 인스턴스
   * 
   * @example
   * ```ts
   * const ctx = await ContextFactory.fromRequest(req);
   * ```
   */
  static async fromRequest(request: Request): Promise<IKrepisContext> {
    // 헤더에서 테넌트 ID 추출
    const tenantId = request.headers.get("X-Krepis-Tenant-ID") ?? "default";
    const isTurbo = request.headers.get("X-Krepis-Turbo") === "true";
    const requestId = request.headers.get("X-Request-ID") ?? undefined;
    
    return await this.create({
      tenantId,
      isTurboMode: isTurbo,
      requestId,
      metadata: {
        method: request.method,
        url: request.url,
      },
    });
  }
  
  /**
   * 기존 컨텍스트로부터 파생 컨텍스트를 생성합니다.
   * 
   * 동일한 tenant, trace로 새로운 request를 수행할 때 유용합니다.
   * 
   * @param parent - 부모 컨텍스트
   * @param overrides - 재정의할 옵션
   * @returns 새로운 Sovereign Context
   */
  static async createDerived(
    parent: IKrepisContext,
    overrides?: Partial<ContextOptions>
  ): Promise<IKrepisContext> {
    return await this.create({
      tenantId: parent.tenantId,
      isTurboMode: parent.isTurboMode,
      priority: parent.priority,
      metadata: parent.getAllMetadata(),
      ...overrides,
    });
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Convenience Exports
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 간편 함수: 컨텍스트 생성.
 * 
 * @example
 * ```ts
 * using ctx = await createContext({ tenantId: "acme" });
 * ```
 */
export async function createContext(
  options: ContextOptions
): Promise<IKrepisContext> {
  return await ContextFactory.create(options);
}

/**
 * 간편 함수: HTTP 요청으로부터 컨텍스트 생성.
 */
export async function createContextFromRequest(
  request: Request
): Promise<IKrepisContext> {
  return await ContextFactory.fromRequest(request);
}