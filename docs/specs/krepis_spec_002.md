# **📑 \[Krepis-Spec-002\] Dependency Injection Module Specification (v1.1.0)**

**버전:** v1.1.0 (Architecture Guard & Context Integrated)

**상태:** Final Draft

**모듈명:** @krepis/core/di

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Zero-Reflection Core:** reflect-metadata 없이 정적 분석만으로 의존성을 해결하여 런타임 성능을 극대화합니다.  
2. **Context-Aware Scoping:** AsyncLocalStorage와 결합하여 별도의 인자 전달 없이도 요청 단위의 객체 격리(Isolation)를 자동화합니다.  
3. **Fail-Fast Validation:** 순환 참조, 의존성 누락, 파라미터 불일치를 인스턴스화 시점이 아닌 **애플리케이션 부트스트랩 시점**에 검증합니다.  
4. **Interface-First:** 구체 클래스가 아닌 심볼/추상 클래스 기반의 바인딩을 권장하여 헥사고날 아키텍처를 강제합니다.

---

## **Ⅱ. 핵심 메커니즘 고도화**

### **1\. 서비스 식별자 및 불변 바인딩**

인터페이스 기반 개발을 위해 Token 시스템을 표준화합니다.

TypeScript

export class InjectionToken\<T\> {  
  constructor(public readonly description: string) {}  
}

export type ServiceIdentifier\<T\> \= InjectionToken\<T\> | (new (...args: any\[\]) \=\> T) | symbol;

### **2\. 정적 의존성 검증 (Validation Guard)**

개발자가 static inject와 constructor의 순서를 틀리는 실수를 방지합니다.

TypeScript

export interface IInjectable {  
  readonly inject: ServiceIdentifier\<any\>\[\];  
}

// 부트스트랩 시 검증 로직  
if (Implementation.length \!== (Implementation as any).inject?.length) {  
  throw new Error(\`KrepisDIError: Parameter count mismatch in ${Implementation.name}\`);  
}

---

## **Ⅲ. 상세 API 및 라이프사이클 (ALS 통합)**

### **1\. IServiceProvider (Scope Auto-Management)**

@krepis/context와 결합하여 현재 비동기 흐름에 맞는 컨테이너를 자동으로 반환합니다.

TypeScript

export interface IServiceProvider {  
  /\*\* 현재 컨텍스트(ALS)에 종속된 객체 해결 \*/  
  get\<T\>(id: ServiceIdentifier\<T\>): T;  
    
  /\*\* 테스트 및 특수 상황을 위한 수동 스코프 생성 \*/  
  createScope(): IServiceScope;  
}

### **2\. 순환 참조 탐지 엔진 (Circular Guard)**

TypeScript

// 내부 해결 로직 (Pseudo-code)  
resolve\<T\>(id: ServiceIdentifier\<T\>, resolutionStack: Set\<ServiceIdentifier\<any\>\>): T {  
  if (resolutionStack.has(id)) {  
    throw new Error(\`KrepisDIError: Circular dependency detected: ${Array.from(resolutionStack).join(' \-\> ')} \-\> ${id}\`);  
  }  
  resolutionStack.add(id);  
  // ... 인스턴스 생성 로직  
  resolutionStack.delete(id);  
}

---

## **Ⅳ. 모듈화 및 확장 전략**

### **1\. IServiceModule (분산 등록)**

거대한 등록 파일을 방지하기 위해 도메인별 모듈 등록 방식을 지원합니다.

TypeScript

export interface IServiceModule {  
  configure(services: IServiceCollection): void;  
}

// 사용 예시  
const app \= new KrepisApplication();  
app.addModule(new OrderDomainModule());  
app.addModule(new InfrastructureModule());

### **2\. Mocking & Override (Testing Support)**

테스트 환경에서 특정 의존성을 즉시 교체할 수 있는 기능을 제공합니다.

TypeScript

services.replace(IUserRepository, new MockUserRepository());

---

## **Ⅴ. Context 통합 파이프라인 (The Auto-Scope)**

RequestContext.run 시점에 DI 스코프를 함께 생성하여 전파하는 메커니즘입니다.

TypeScript

export class DiContextBehavior implements IPipelineBehavior {  
  constructor(private readonly rootProvider: IServiceProvider) {}

  async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
    const scope \= this.rootProvider.createScope();  
      
    // RequestContext에 스코프된 ServiceProvider를 주입  
    return RequestContext.run(  
      ctx.store.set(DI\_CONTAINER, scope.serviceProvider),   
      async () \=\> {  
        try {  
          return await next();  
        } finally {  
          scope.dispose(); // 요청 종료 시 스코프 내 Transient/Scoped 객체 자동 정리  
        }  
      }  
    );  
  }  
}

---

## **Ⅵ. 기대 효과 (KPI)**

1. **신뢰성(Reliability):** 애플리케이션 기동 시 모든 의존성 그래프의 무결성 검증 완료.  
2. **생산성(DX):** RequestContext.current().get(ID)를 통해 어디서든 타입 안전하게 객체 획득.  
3. **성능(Latency):** 리플렉션 비용 제거로 인해 기존 DI 엔진 대비 인스턴스 생성 속도 약 20% 향상.

---
