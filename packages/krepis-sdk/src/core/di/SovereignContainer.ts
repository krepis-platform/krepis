/**
 * @file SovereignContainer.ts
 * @version 1.0.0
 * @spec [Spec-002] DI Module v1.2.0
 * 
 * Krepis Sovereign DI Container 구현.
 * 
 * 특징:
 * 1. Context-Bound Lifetime - 각 컨텍스트마다 독립적인 스코프
 * 2. Explicit Resolution - ctx를 통한 명시적 의존성 해결
 * 3. AOT Validation - 부트스트랩 시점에 의존성 그래프 검증
 */

import type { IKrepisContext } from "../context/IKrepisContext.ts";
import type {
  ServiceIdentifier,
  ServiceDescriptor,
  IScopedContainer,
  IServiceProvider,
  IServiceCollection,
  Constructor,
} from "./identifiers.ts";
import {
  ServiceLifetime as Lifetime,
  KREPIS_CONTEXT,
} from "./identifiers.ts";


/**
 * 내부 인스턴스 생성을 위한 구체적인 생성자 타입 정의
 */
type ConcreteConstructor<T> = new (...args: any[]) => T;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Service Collection Implementation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 서비스 등록 빌더 구현.
 */
export class ServiceCollection implements IServiceCollection {
  private readonly descriptors: Map<ServiceIdentifier<unknown>, ServiceDescriptor<unknown>> = new Map();
  
  addSingleton<T>(
    id: ServiceIdentifier<T>,
    implementation: Constructor<T> | ((provider: IServiceProvider) => T),
    dependencies?: ServiceIdentifier<unknown>[]
  ): this {
    this.descriptors.set(id as ServiceIdentifier<unknown>, {
      identifier: id as ServiceIdentifier<unknown>,
      lifetime: Lifetime.Singleton,
      implementation: implementation as any,
      dependencies,
    });
    return this;
  }
  
  addScoped<T>(
    id: ServiceIdentifier<T>,
    implementation: Constructor<T> | ((container: IScopedContainer) => T),
    dependencies?: ServiceIdentifier<unknown>[]
  ): this {
    this.descriptors.set(id as ServiceIdentifier<unknown>, {
      identifier: id as ServiceIdentifier<unknown>,
      lifetime: Lifetime.Scoped,
      implementation: implementation as any,
      dependencies,
    });
    return this;
  }
  
  addTransient<T>(
    id: ServiceIdentifier<T>,
    implementation: Constructor<T> | ((container: IScopedContainer) => T),
    dependencies?: ServiceIdentifier<unknown>[]
  ): this {
    this.descriptors.set(id as ServiceIdentifier<unknown>, {
      identifier: id as ServiceIdentifier<unknown>,
      lifetime: Lifetime.Transient,
      implementation: implementation as any,
      dependencies,
    });
    return this;
  }
  
  build(): IServiceProvider {
    if (!this.descriptors.has(KREPIS_CONTEXT as ServiceIdentifier<unknown>)) {
      this.descriptors.set(KREPIS_CONTEXT as ServiceIdentifier<unknown>, {
        identifier: KREPIS_CONTEXT as ServiceIdentifier<unknown>,
        lifetime: Lifetime.Scoped,
        implementation: () => { throw new Error("Internal use only"); },
      });
    }
    
    this.validateDependencyGraph();
    return new SovereignServiceProvider(new Map(this.descriptors));
  }
  
  private validateDependencyGraph(): void {
    for (const [id, descriptor] of this.descriptors) {
      if (descriptor.dependencies) {
        for (const dep of descriptor.dependencies) {
          if (!this.descriptors.has(dep)) {
            const idName = typeof id === "function" ? id.name : String(id);
            const depName = typeof dep === "function" ? dep.name : String(dep);
            throw new Error(`[ServiceCollection] Missing dependency: ${depName} required by ${idName}`);
          }
        }
      }
    }
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Root Service Provider Implementation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Root Service Provider 구현.
 */
class SovereignServiceProvider implements IServiceProvider {
  private readonly singletons: Map<ServiceIdentifier<unknown>, unknown> = new Map();
  
  constructor(
    private readonly descriptors: Map<ServiceIdentifier<unknown>, ServiceDescriptor<unknown>>
  ) {
    for (const [id, descriptor] of descriptors) {
      if (descriptor.lifetime === Lifetime.Singleton) {
        this.singletons.set(id, this.createInstance(descriptor, null));
      }
    }
  }
  
  getSingleton<T>(id: ServiceIdentifier<T>): T {
    const idKey = id as ServiceIdentifier<unknown>;
    if (this.singletons.has(idKey)) {
      return this.singletons.get(idKey) as T;
    }
    
    const descriptor = this.descriptors.get(idKey);
    if (!descriptor || descriptor.lifetime !== Lifetime.Singleton) {
      throw new Error(`[ServiceProvider] Singleton service not found: ${String(id)}`);
    }
    
    const instance = this.createInstance(descriptor, null);
    this.singletons.set(idKey, instance);
    return instance as T;
  }
  
  createScope(ctx: IKrepisContext): IScopedContainer {
    return new SovereignScopedContainer(this.descriptors, ctx, this);
  }
  
  has<T>(id: ServiceIdentifier<T>): boolean {
    return this.descriptors.has(id as ServiceIdentifier<unknown>);
  }
  
  private createInstance(
    descriptor: ServiceDescriptor<unknown>,
    container: IScopedContainer | IServiceProvider | null
  ): unknown {
    const impl = descriptor.implementation;
    
    if (typeof impl === "function") {
      if (!impl.prototype) {
        return (impl as (c: unknown) => unknown)(container);
      }
      
      const ConstructorRef = impl as ConcreteConstructor<unknown>;
      if (descriptor.dependencies && descriptor.dependencies.length > 0) {
        const deps = descriptor.dependencies.map((dep) => {
          if (this.singletons.has(dep)) return this.singletons.get(dep);
          throw new Error(`[ServiceProvider] Cannot resolve static dependency: ${String(dep)}`);
        });
        return new ConstructorRef(...deps);
      }
      return new ConstructorRef();
    }
    return impl;
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Scoped Container Implementation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Scoped DI Container 구현.
 * 
 * 각 IKrepisContext마다 하나의 인스턴스가 생성됩니다.
 */
class SovereignScopedContainer implements IScopedContainer {
  private readonly scopedInstances: Map<ServiceIdentifier<unknown>, unknown> = new Map();
  private disposed = false;
  
  constructor(
    private readonly descriptors: Map<ServiceIdentifier<unknown>, ServiceDescriptor<unknown>>,
    private readonly ctx: IKrepisContext,
    private readonly root: IServiceProvider 
  ) {
    this.scopedInstances.set(KREPIS_CONTEXT as ServiceIdentifier<unknown>, this.ctx);
  }
  
  get<T>(id: ServiceIdentifier<T>): T {
    this.ensureNotDisposed();
    const idKey = id as ServiceIdentifier<unknown>;
    
    if (this.scopedInstances.has(idKey)) {
      return this.scopedInstances.get(idKey) as T;
    }
    
    const descriptor = this.descriptors.get(idKey);
    if (!descriptor) {
      throw new Error(`[ScopedContainer] Service not found: ${String(id)}`);
    }
    
    if (descriptor.lifetime === Lifetime.Singleton) {
      return this.root.getSingleton(id);
    }
    
    const instance = this.createInstance(descriptor);
    if (descriptor.lifetime === Lifetime.Scoped) {
      this.scopedInstances.set(idKey, instance);
    }
    
    return instance as T;
  }
  
  has<T>(id: ServiceIdentifier<T>): boolean {
    return this.descriptors.has(id as ServiceIdentifier<unknown>);
  }
  
  [Symbol.dispose](): void {
    if (this.disposed) return;
    
    for (const [id, instance] of this.scopedInstances) {
      if (id === (KREPIS_CONTEXT as ServiceIdentifier<unknown>)) {
        continue; 
      }
      
      if (isDisposable(instance)) {
        instance[Symbol.dispose]();
      }
    }
    
    this.scopedInstances.clear();
    this.disposed = true;
  }
  
  private createInstance(descriptor: ServiceDescriptor<unknown>): unknown {
    const impl = descriptor.implementation;
    
    if (typeof impl === "function") {
      if (!impl.prototype) {
        return (impl as (c: IScopedContainer) => unknown)(this);
      }
      
      // ⚠️ 핵심 수정: AbstractConstructor를 ConcreteConstructor로 단언하여 'new' 호출 허용
      const ConstructorRef = impl as ConcreteConstructor<unknown>;
      if (descriptor.dependencies && descriptor.dependencies.length > 0) {
        const deps = descriptor.dependencies.map((dep) => this.get(dep as ServiceIdentifier<unknown>));
        return new ConstructorRef(...deps);
      }
      return new ConstructorRef();
    }
    return impl;
  }
  
  private ensureNotDisposed(): void {
    if (this.disposed) throw new Error("[ScopedContainer] Container is disposed");
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4] Convenience Exports
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 객체가 Disposable 인터페이스를 구현하는지 확인하는 Type Guard
 */
function isDisposable(obj: unknown): obj is Disposable {
  if (!obj || typeof obj !== "object") return false;
  return Symbol.dispose in obj && typeof (obj as Record<symbol, unknown>)[Symbol.dispose] === "function";
}

/**
 * 새로운 ServiceCollection을 생성합니다.
 * 
 * @example
 * ```ts
 * const services = createServiceCollection();
 * services.addSingleton(LOGGER, ConsoleLogger);
 * const provider = services.build();
 * ```
 */
export function createServiceCollection(): IServiceCollection {
  return new ServiceCollection();
}