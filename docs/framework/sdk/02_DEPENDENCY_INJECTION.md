# 📑 

 Dependency Injection Module Specification (v1.2.0)

**버전:** v1.2.0 (Explicit Context Driven & Zero-Reflection)

**상태:** Final Draft

**모듈명:** @krepis/core/di

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Context-Bound Lifetime:** 모든 객체는 커널로부터 부여받은 `IKrepisContext`의 생명주기에 결속됩니다.
2. **Explicit Dependency Resolution:** 암시적인 전역 조회를 배제하고, `ctx`를 통해 현재 요청에 격리된 의존성을 명시적으로 획득합니다.
3. **AOT(Ahead-Of-Time) Validation:** 부트스트랩 시점에 전체 의존성 그래프를 검증하여 런타임 중 `Dependency Missing` 에러를 원천 차단합니다.
4. **Sovereign Isolation:** 테넌트별 리소스 제한이 DI 레이어에서도 반영되도록, 각 스코프는 테넌트의 정책 정보를 포함합니다.

---

## **Ⅱ. 핵심 메커니즘 고도화**

### **1. Explicit Contextual Token**

서비스 식별자는 이제 컨텍스트 정보와 결합하여 해결됩니다.

```typescript
export class InjectionToken<T> {
  constructor(public readonly description: string) {}
}

export type ServiceIdentifier<T> = InjectionToken<T> | (new (...args: any[]) => T) | symbol;

```

### **2. IServiceProvider (The Sovereign Resolver)**

더 이상 `RequestContext.current()`를 쓰지 않고, 인자로 받은 `ctx`를 통해 객체를 해결합니다.

```typescript
export interface IServiceProvider {
  /**
   * 명시적으로 전달된 ctx를 기반으로 객체 해결 (Scoped/Transient)
   */
  get<T>(ctx: IKrepisContext, id: ServiceIdentifier<T>): T;
  
  /**
   * 싱글톤 또는 전역 서비스 해결 (Context-free)
   */
  getGlobal<T>(id: ServiceIdentifier<T>): T;
}

```

---

## **Ⅲ. 상세 라이프사이클 및 스코핑**

### **1. Scope Mapping (Context ↔ Container)**

요청이 들어오면 커널의 `IKrepisContext`와 1:1로 매핑되는 `IServiceScope`가 생성됩니다.

### **2. Disposable Scope Management**

`Symbol.dispose`를 통해 `ctx`가 해제될 때 스코프 내의 객체들도 함께 정리됩니다.

```typescript
export interface IServiceScope extends Disposable {
  readonly serviceProvider: IServiceProvider;
  readonly context: IKrepisContext;
}

```

---

## **Ⅳ. 모듈화 및 확장 전략**

### **1. IInjectable (Static Dependency Declaration)**

런타임 성능을 위해 리플렉션 대신 정적 프로퍼티를 사용합니다.

```typescript
export interface IInjectable {
  // 의존성 목록을 정적으로 정의
  static readonly inject: ServiceIdentifier<any>[];
}

// 예시: 명시적 주입을 받는 서비스
export class OrderService implements IInjectable {
  static readonly inject = [IUserRepository, IPaymentGateway];

  constructor(
    private readonly users: IUserRepository,
    private readonly payment: IPaymentGateway
  ) {}

  async createOrder(ctx: IKrepisContext, orderData: any) {
    // 하위 의존성 호출 시 ctx를 명시적으로 전파
    const user = await this.users.findById(ctx, orderData.userId);
    // ...
  }
}

```

---

## **Ⅴ. Context 통합 파이프라인 (Explicit Flow)**

파이프라인 단계에서 `ctx`와 `scope`를 생성하여 다음 핸들러로 전달합니다.

```typescript
export class DiContextBehavior implements IPipelineBehavior {
  constructor(private readonly rootProvider: IServiceProvider) {}

  async handle(rawRequest: any, next: NextPipe<any>) {
    // 1. 커널 컨텍스트 생성 (Sovereign Bridge 활용)
    using ctx = await SovereignContextBridge.fromRequest(rawRequest);
    
    // 2. 해당 컨텍스트에 묶인 DI 스코프 생성
    using scope = this.rootProvider.createScope(ctx);

    // 3. 컨텍스트와 스코프를 하위 파이프로 명시적 전달
    return await next(ctx, scope.serviceProvider);
  }
}

```

---

## **Ⅵ. 기대 효과 (KPI)**

1. **인과관계의 명확성:** 어떤 객체가 어떤 요청(`ctx`)에 의해 생성되었는지 100% 추적 가능 (AI 분석 최적화).
2. **메모리 안정성:** `AsyncLocalStorage`의 가비지 컬렉션 지연 문제 해결. `using` 구문으로 요청 종료 즉시 스코프 메모리 해제.
3. **격리성(Isolation):** 테넌트 A의 객체가 테넌트 B의 컨텍스트에서 오염될 가능성을 타입 시스템 수준에서 차단.

---