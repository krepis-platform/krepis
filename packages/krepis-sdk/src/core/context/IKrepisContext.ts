/**
 * @file IKrepisContext.ts
 * @version 1.0.0
 * @spec [Spec-001] Context Propagation v1.2.0
 * @spec [Spec-002] DI Module v1.2.0
 * 
 * Krepis의 핵심 컨텍스트 인터페이스.
 * 모든 비즈니스 로직과 인프라 레이어는 이 컨텍스트를 명시적으로 전달받아야 합니다.
 * 
 * 설계 원칙:
 * 1. Explicit Over Implicit - AsyncLocalStorage 배제
 * 2. Native-Origin Truth - 커널에서 생성된 데이터 소비
 * 3. Zero-Inertia Propagation - 리소스 쿼터와 실행 권한 포함
 * 4. Disposable Lifecycle - using 구문 지원
 */

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Core Context Interface
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Krepis Sovereign Context 인터페이스.
 * 
 * 이 컨텍스트는 단순한 데이터 구조가 아니라, 
 * 리소스 할당권(Quota)과 실행 권한(Authorization)을 담은 '통치권의 증명'입니다.
 * 
 * @example
 * ```ts
 * async function handleRequest(ctx: IKrepisContext, input: any) {
 *   const result = await userService.findUser(ctx, input.userId);
 *   return result;
 * }
 * ```
 */
export interface IKrepisContext extends Disposable {
  // ─────────────────────────────────────────────────────────────────────────────
  // Core Identifiers (Immutable)
  // ─────────────────────────────────────────────────────────────────────────────
  
  /**
   * 요청의 고유 식별자.
   * 로깅, 추적, 디버깅의 기본 키로 사용됩니다.
   */
  readonly requestId: string;
  
  /**
   * 테넌트(Tenant) 식별자.
   * 멀티 테넌시 환경에서 리소스 격리의 기준이 됩니다.
   */
  readonly tenantId: string;
  
  /**
   * 분산 추적(Distributed Tracing) ID.
   * 여러 서비스에 걸친 요청의 흐름을 추적합니다.
   */
  readonly traceId: string;
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Execution Metadata
  // ─────────────────────────────────────────────────────────────────────────────
  
  /**
   * Turbo 모드 활성화 여부.
   * true일 경우 Enterprise 등급의 리소스 할당을 받습니다.
   */
  readonly isTurboMode: boolean;
  
  /**
   * 컨텍스트 생성 시각 (Unix timestamp, milliseconds).
   */
  readonly timestamp: bigint;
  
  /**
   * 실행 우선순위 (0-10).
   * 높을수록 우선 처리됩니다.
   */
  readonly priority: number;
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Binary & Metadata Access
  // ─────────────────────────────────────────────────────────────────────────────
  
  /**
   * Protobuf로 직렬화된 원본 바이너리 데이터.
   * FFI 호출 시 커널로 전달됩니다.
   * 
   * ⚠️ 이 데이터는 직접 수정하지 마십시오.
   */
  readonly binary: Uint8Array;
  
  /**
   * 커스텀 메타데이터 조회.
   * 
   * @param key - 메타데이터 키
   * @returns 값 또는 undefined
   * 
   * @example
   * ```ts
   * const userId = ctx.getMetadata("user_id");
   * const locale = ctx.getMetadata("locale") ?? "en-US";
   * ```
   */
  getMetadata(key: string): string | undefined;
  
  /**
   * 모든 메타데이터를 읽기 전용 레코드로 반환.
   */
  getAllMetadata(): Readonly<Record<string, string>>;
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Lifecycle & Resource Management
  // ─────────────────────────────────────────────────────────────────────────────
  
  /**
   * Explicit Resource Management (ERM) 지원.
   * using 블록 종료 시 자동으로 호출되어 커널 리소스를 해제합니다.
   * 
   * @example
   * ```ts
   * using ctx = await ContextFactory.create({ tenantId: "acme" });
   * // ... 작업 수행 ...
   * // 블록 종료 시 자동으로 [Symbol.dispose] 호출
   * ```
   */
  [Symbol.dispose](): void;
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Context Creation Options
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 컨텍스트 생성 시 전달할 옵션.
 */
export interface ContextOptions {
  /**
   * 테넌트 ID (필수).
   */
  tenantId: string;
  
  /**
   * 요청 ID (선택, 자동 생성 가능).
   */
  requestId?: string;

  /**
   * 추적 ID (필수)
   */
  traceId?: string;
  
  /**
   * Turbo 모드 활성화 (기본값: false).
   */
  isTurboMode?: boolean;
  
  /**
   * 실행 우선순위 (기본값: 5).
   */
  priority?: number;
  
  /**
   * 커스텀 메타데이터.
   */
  metadata?: Record<string, string>;
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Context State & Validation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 컨텍스트의 상태.
 */
export enum ContextState {
  /** 활성 상태 - 정상 사용 가능 */
  Active = "ACTIVE",
  
  /** 폐기됨 - dispose() 호출 후 */
  Disposed = "DISPOSED",
  
  /** 타임아웃 - 실행 시간 초과 */
  TimedOut = "TIMED_OUT",
  
  /** 에러 - 커널 에러 발생 */
  Faulted = "FAULTED",
}

/**
 * 컨텍스트 검증 결과.
 */
export interface ContextValidation {
  /** 검증 통과 여부 */
  isValid: boolean;
  
  /** 에러 메시지 (실패 시) */
  errors?: string[];
  
  /** 경고 메시지 */
  warnings?: string[];
}

/**
 * 컨텍스트 검증 유틸리티.
 */
export class ContextValidator {
  /**
   * ContextOptions의 유효성을 검증합니다.
   * 
   * @param options - 검증할 옵션
   * @returns 검증 결과
   */
  static validate(options: ContextOptions): ContextValidation {
    const errors: string[] = [];
    const warnings: string[] = [];
    
    // 필수 필드 검증
    if (!options.tenantId) {
      errors.push("tenantId is required");
    } else if (options.tenantId.length === 0) {
      errors.push("tenantId cannot be empty");
    }
    
    // 우선순위 범위 검증
    if (options.priority !== undefined) {
      if (options.priority < 0 || options.priority > 10) {
        errors.push("priority must be between 0 and 10");
      }
    }
    
    // 메타데이터 키 검증
    if (options.metadata) {
      for (const key of Object.keys(options.metadata)) {
        if (key.includes(" ") || key.includes(":")) {
          warnings.push(`metadata key '${key}' contains special characters`);
        }
      }
    }
    
    return {
      isValid: errors.length === 0,
      errors: errors.length > 0 ? errors : undefined,
      warnings: warnings.length > 0 ? warnings : undefined,
    };
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4] Type Guards
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 객체가 IKrepisContext 인터페이스를 구현하는지 확인합니다.
 */
export function isKrepisContext(obj: unknown): obj is IKrepisContext {
  if (!obj || typeof obj !== "object") {
    return false;
  }

  const candidate = obj as Record<string | symbol, unknown>;
  
  return (
    typeof candidate.requestId === "string" &&
    typeof candidate.tenantId === "string" &&
    typeof candidate.traceId === "string" &&
    typeof candidate.isTurboMode === "boolean" &&
    typeof candidate.timestamp === "bigint" &&
    candidate.binary instanceof Uint8Array &&
    typeof candidate.getMetadata === "function" &&
    // Symbol.dispose를 안전하게 체크
    typeof candidate[Symbol.dispose] === "function"
  );
}

/**
 * 컨텍스트가 폐기되었는지 확인합니다.
 * 
 * 폐기된 컨텍스트를 사용하려 시도하면 에러가 발생합니다.
 */
export function isDisposed(ctx: IKrepisContext): boolean {
  const internal = ctx as unknown as { _state?: ContextState };
  return internal._state === ContextState.Disposed;
}