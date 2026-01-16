# **📑 \[Krepis-Spec-010\] Unified Pipeline & Middleware Specification (v1.1.0)**

**버전:** v1.1.0 (Scoped Execution & Legacy Adapter 확장)

**상태:** Final Draft

**모듈명:** @krepis/pipeline

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **True Unification:** HTTP 미들웨어, Guard, Interceptor, CQRS Behavior를 단일 IPipelineBehavior로 통합하여 아키텍트적 복잡성을 제거합니다.  
2. **Zero-Allocation Path:** 요청 처리 시마다 클로저(Closure)를 생성하지 않고, 사전에 정렬된 정적 배열 인덱스를 제어하여 최상의 Throughput을 달성합니다.  
3. **Scoped execution:** 전역(Global), 그룹(Scoped), 핸들러(Local) 단위의 Behavior를 지능적으로 병합하여 동적 분기를 지원합니다.  
4. **Graceful Short-circuiting:** 인증 실패 등으로 파이프라인이 중단되어도, Post-process 영역(로깅, 메트릭)은 반드시 실행됨을 보장합니다.

---

## **Ⅱ. 핵심 데이터 구조 및 인터페이스**

### **1\. 확장된 Pipeline Context**

TypeScript

export interface PipelineContext\<TRequest \= any\> {  
  readonly request: TRequest;  
  readonly metadata: {  
    readonly schema: 'http' | 'grpc' | 'event';  
    readonly path: string;              // 요청 경로 (분기용)  
    readonly startTime: number;  
    readonly shortCircuitPoint?: string; // 중단된 지점 기록  
  };  
  readonly services: IServiceProvider;  // Scoped DI  
  readonly context: IContextStore;      // Spec-001 하이브리드 컨텍스트  
  readonly items: Map\<symbol, any\>;     // 타입 안전성을 위한 Symbol 키 사용  
}

### **2\. IPipelineBehavior (The Unit)**

TypeScript

export type NextPipe\<TRes\> \= () \=\> Promise\<Result\<TRes\>\>;

export interface IPipelineBehavior\<TReq \= any, TRes \= any\> {  
  /\*\*  
   \* @param ctx 파이프라인 문맥  
   \* @param next 다음 단계 실행 함수. 호출하지 않으면 파이프라인 중단(Short-circuit).  
   \*/  
  handle(ctx: PipelineContext\<TReq\>, next: NextPipe\<TRes\>): Promise\<Result\<TRes\>\>;  
}

---

## **Ⅲ. 고도화된 실행 엔진 (The Pipeline Engine)**

### **1\. Scoped Chain Builder (동적 분기 전략)**

요청 시마다 체인을 조립하는 대신, 경로/메타데이터별로 최적화된 실행 배열을 캐싱합니다.

TypeScript

export class PipelineProvider {  
  private readonly chainCache \= new Map\<string, IPipelineBehavior\[\]\>();

  getChain(path: string, handlerBehaviors: IPipelineBehavior\[\]): IPipelineBehavior\[\] {  
    if (this.chainCache.has(path)) return this.chainCache.get(path)\!;

    // Global \-\> Scoped (Group) \-\> Local (Handler) 순으로 정적 병합  
    const merged \= \[...this.globalBehaviors, ...this.scopedBehaviors, ...handlerBehaviors\];  
    this.chainCache.set(path, merged);  
    return merged;  
  }  
}

### **2\. Zero-Allocation Executor (정적 순회)**

TypeScript

export class PipelineExecutor {  
  async execute\<TReq, TRes\>(  
    behaviors: IPipelineBehavior\[\],  
    ctx: PipelineContext\<TReq\>,  
    finalHandler: () \=\> Promise\<Result\<TRes\>\>  
  ): Promise\<Result\<TRes\>\> {  
    let index \= 0;

    const next: NextPipe\<TRes\> \= async () \=\> {  
      if (index \< behaviors.length) {  
        const behavior \= behaviors\[index++\];  
        return await behavior.handle(ctx, next);  
      }  
      return await finalHandler();  
    };

    return await next();  
  }  
}

---

## **Ⅳ. 레거시 호환 및 응답 매핑**

### **1\. Legacy Middleware Adapter**

기존 Express/Fastify 미들웨어를 Krepis 파이프라인으로 흡수합니다.

TypeScript

export class HttpMiddlewareAdapter implements IPipelineBehavior {  
  constructor(private legacyMiddleware: (req: any, res: any, next: any) \=\> void) {}

  async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
    return new Promise\<Result\<any\>\>((resolve) \=\> {  
      this.legacyMiddleware(ctx.request.rawReq, ctx.request.rawRes, async (err: any) \=\> {  
        if (err) resolve(Fail({ code: 'LEGACY\_ERROR', message: err.message }));  
        else resolve(await next());  
      });  
    });  
  }  
}

---

## **Ⅴ. 파이프라인 계층 예시 (Standard Order)**

1. **ContextBridge:** AsyncLocalStorage 경계 설정 및 TraceId 발급.  
2. **GlobalLogging:** 요청 유입 및 최종 결과 로깅 (Post-process 영역 활용).  
3. **Resilience:** Circuit Breaker, Retry (Spec-008).  
4. **Authentication/Guard:** 권한 검증 및 파이프라인 중단 제어.  
5. **Validation:** Specification 기반 요청 값 검증 (Spec-009).  
6. **Transaction:** Unit of Work 시작 및 커밋/롤백 (Spec-005).  
7. **Domain Handler (Target):** 실제 비즈니스 로직 실행.

---

## **Ⅵ. 기대 효과 (KPI)**

1. **운영 안정성:** 모든 요청이 동일한 ContextBridge를 통과하여 분산 트레이싱 가시성 100% 확보.  
2. **성능 최적화:** 동적 함수 생성을 배제하여 대규모 트래픽 상황에서 메모리 할당 오버헤드 최소화.  
3. **확장성:** 신규 프로토콜(예: 웹소켓) 도입 시 PipelineContext만 확장하여 기존 비즈니스 로직(Behavior) 재사용 가능.

---
