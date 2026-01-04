/**
 * @file identifiers.ts
 * @version 1.0.0
 * @spec [Spec-002] DI Module v1.2.0
 * 
 * Krepis Dependency Injection 식별자 및 타입 정의.
 * 
 * 설계 원칙:
 * 1. Explicit Dependency Resolution - 암시적 조회 배제
 * 2. Type-Safe Injection - ServiceIdentifier<T>로 타입 보장
 * 3. AOT Validation - 부트스트랩 시점에 의존성 검증
 */

import type { IKrepisContext } from "../context/IKrepisContext.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Service Identifier Types
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 서비스 식별자를 위한 추상 토큰.
 * 
 * @example
 * ```ts
 * const LOGGER = new InjectionToken<ILogger>("ILogger");
 * ```
 */
export class InjectionToken<T> {
  // _ref는 런타임에 존재하지 않으며 타입 시스템에서만 작동합니다.
  declare readonly _type: T;

  constructor(public readonly description: string) {}
  
  toString(): string {
    return `InjectionToken(${this.description})`;
  }
}

/**
 * 서비스 식별자 타입.
 * 
 * - InjectionToken<T>: 추상 토큰
 * - Constructor<T>: 클래스 생성자
 * - symbol: 고유 심볼
 */
export type ServiceIdentifier<T> =
  | InjectionToken<T>
  | Constructor<T>
  | symbol;

/**
 * 생성자 타입.
 */
export type Constructor<T> = abstract new (...args: never[]) => T;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Service Lifetime
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 서비스 생명주기.
 */
export enum ServiceLifetime {
  /**
   * 싱글톤 - 애플리케이션 전체에서 하나의 인스턴스.
   * Context-free 서비스에 적합 (Configuration, Logger 등).
   */
  Singleton = "SINGLETON",
  
  /**
   * Scoped - 각 Context마다 하나의 인스턴스.
   * Context-bound 서비스에 적합 (Repository, UnitOfWork 등).
   */
  Scoped = "SCOPED",
  
  /**
   * Transient - 요청마다 새 인스턴스.
   * 상태가 없는 서비스에 적합 (Factory, Builder 등).
   */
  Transient = "TRANSIENT",
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Service Descriptor
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 서비스 등록 정보.
 */
export interface ServiceDescriptor<T = unknown> {
  identifier: ServiceIdentifier<T>;
  lifetime: ServiceLifetime;
  implementation:
    | Constructor<T>
    | ((container: IScopedContainer) => T);

  dependencies?: ServiceIdentifier<unknown>[];
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4] Container Interfaces
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Scoped DI Container 인터페이스.
 * 
 * 각 IKrepisContext는 자신만의 ScopedContainer를 가지며,
 * 이를 통해 의존성을 해결합니다.
 */
export interface IScopedContainer extends Disposable {
  /**
   * 서비스 인스턴스를 가져옵니다.
   * 
   * @param id - 서비스 식별자
   * @returns 서비스 인스턴스
   * @throws {Error} 서비스를 찾을 수 없는 경우
   */
  get<T>(id: ServiceIdentifier<T>): T;
  
  /**
   * 서비스가 등록되어 있는지 확인합니다.
   */
  has<T>(id: ServiceIdentifier<T>): boolean;
  
  /**
   * 컨테이너를 폐기합니다.
   * Scoped 인스턴스들도 함께 정리됩니다.
   */
  [Symbol.dispose](): void;
}

/**
 * Root Service Provider 인터페이스.
 * 
 * 애플리케이션 부트스트랩 시 생성되며, 
 * Context별 Scoped Container를 생성합니다.
 */
export interface IServiceProvider {
  /**
   * Singleton 서비스를 가져옵니다 (Context-free).
   */
  getSingleton<T>(id: ServiceIdentifier<T>): T;
  
  /**
   * 새로운 Scoped Container를 생성합니다.
   * 
   * @param ctx - Context (Scoped 서비스 생성에 사용)
   * @returns Scoped Container
   */
  createScope(ctx: IKrepisContext): IScopedContainer;
  
  /**
   * 서비스가 등록되어 있는지 확인합니다.
   */
  has<T>(id: ServiceIdentifier<T>): boolean;
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [5] Service Collection (Builder)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 서비스 등록 빌더.
 * 
 * @example
 * ```ts
 * const services = new ServiceCollection();
 * services.addSingleton(LOGGER, ConsoleLogger);
 * services.addScoped(USER_REPO, UserRepository, [DATABASE]);
 * 
 * const provider = services.build();
 * ```
 */
export interface IServiceCollection {
  addSingleton<T>(
    id: ServiceIdentifier<T>,
    implementation: Constructor<T> | ((provider: IServiceProvider) => T),
    dependencies?: ServiceIdentifier<unknown>[]
  ): this;
  
  addScoped<T>(
    id: ServiceIdentifier<T>,
    implementation: Constructor<T> | ((container: IScopedContainer) => T),
    dependencies?: ServiceIdentifier<unknown>[]
  ): this;
  
  addTransient<T>(
    id: ServiceIdentifier<T>,
    implementation: Constructor<T> | ((container: IScopedContainer) => T),
    dependencies?: ServiceIdentifier<unknown>[]
  ): this;
  
  build(): IServiceProvider;
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [6] Built-in Service Identifiers
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 내장 서비스 식별자.
 */
export const KREPIS_CONTEXT = new InjectionToken<IKrepisContext>("IKrepisContext");
export const LOGGER = new InjectionToken<ILogger>("ILogger");
export const TELEMETRY = new InjectionToken<ITelemetry>("ITelemetry");

export interface ILogger {
  // any[] 대신 unknown[] 사용
  debug(message: string, ...args: unknown[]): void;
  info(message: string, ...args: unknown[]): void;
  warn(message: string, ...args: unknown[]): void;
  error(message: string, ...args: unknown[]): void;
}

export interface ITelemetry {
  recordMetric(name: string, value: number, ctx: IKrepisContext): void;
  recordEvent(name: string, properties: Record<string, unknown>, ctx: IKrepisContext): void;
}