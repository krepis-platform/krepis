# **📑 \[Krepis-Spec-003\] Unified Pipeline & CQRS Specification (v1.1.0)**

**버전:** v1.1.0 (Cancellation & Error-Type Safety 확장)

**상태:** Final Draft

**모듈명:** @krepis/pipeline, @krepis/cqrs

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Railway Oriented Programming:** 모든 흐름은 Result\<T, E\>라는 선로를 따라 이동하며, 예외(Exception)로 인한 흐름 이탈을 원천 차단합니다.  
2. **Unified Execution:** 외부 진입점(HTTP, gRPC, CLI)에 상관없이 동일한 IPipelineBehavior를 통해 비즈니스 로직에 도달합니다.  
3. **Cancellation-Aware:** 장기 실행 작업의 자원 낭비를 막기 위해 모든 파이프라인 단계는 AbortSignal을 전파합니다.  
4. **Static Logic Mapping:** CLI를 통한 빌드 타임 핸들러 매핑으로 런타임 성능 저하를 방지합니다.

---

## **Ⅱ. 핵심 데이터 규격 (Data Contract)**

### **1\. 고도화된 Result 객체 (with AppError)**

단순한 Error가 아닌, 비즈니스 의미를 담은 IAppError를 포함합니다.

TypeScript

export interface IAppError {  
  readonly code: string;       // 예: 'USER\_NOT\_FOUND'  
  readonly message: string;    // 사용자 메시지  
  readonly details?: any;      // 디버깅 정보  
  readonly originalError?: any; // 원본 시스템 에러 (내부 로깅용)  
}

export type Result\<T, E extends IAppError \= IAppError\> \=   
  | { success: true; value: T; timestamp: number }  
  | { success: false; error: E; timestamp: number };

### **2\. Pipeline Context (v1.1.0 확장)**

TypeScript

export interface PipelineContext\<TRequest \= any\> {  
  readonly request: TRequest;  
  readonly services: IServiceProvider;  
  readonly signal: AbortSignal;         // 실행 중단 신호  
  readonly store: IContextStore;        // Spec-001의 컨텍스트 스토어  
  readonly metadata: {  
    readonly schema: string;            // 'http', 'grpc', 'internal'  
    readonly timestamp: number;  
  };  
}

---

## **Ⅲ. 파이프라인 처리 인터페이스 (Behavior)**

### **1\. 통합 프로세서 (Behavior)**

next() 이전은 Pre-process, 이후는 Post-process 영역으로 활용합니다.

TypeScript

export type NextPipe\<TRes\> \= () \=\> Promise\<Result\<TRes\>\>;

export interface IPipelineBehavior\<TReq \= any, TRes \= any\> {  
  handle(  
    ctx: PipelineContext\<TReq\>,   
    next: NextPipe\<TRes\>  
  ): Promise\<Result\<TRes\>\>;  
}

---

## **Ⅳ. CQRS 핸들러 구조**

### **1\. BaseHandler (Static Metadata 포함)**

TypeScript

export abstract class BaseHandler\<TReq, TRes\> {  
  static inject \= \[\];  
  /\*\* 이 핸들러에서 건너뛸 전역 Behavior 목록 (예: Auth) \*/  
  static skipBehaviors?: string\[\];

  async execute(command: TReq, ctx: PipelineContext): Promise\<Result\<TRes\>\> {  
    if (ctx.signal.aborted) return Fail({ code: 'ABORTED', message: 'Request cancelled' });  
      
    try {  
      return await this.handle(command, ctx);  
    } catch (err) {  
      // 예상치 못한 런타임 에러를 시스템 AppError로 변환  
      return Fail({ code: 'INTERNAL\_ERROR', message: 'An unexpected error occurred', originalError: err });  
    }  
  }

  protected abstract handle(command: TReq, ctx: PipelineContext): Promise\<Result\<TRes\>\>;  
}

---

## **Ⅴ. 방어적 파이프라인 구현 (Implementation)**

### **1\. Cancellation & Timeout Behavior**

TypeScript

export class TimeoutBehavior implements IPipelineBehavior {  
  async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
    const controller \= new AbortController();  
    const timeoutId \= setTimeout(() \=\> controller.abort(), 30000); // 30초 제한

    try {  
      // 기존 signal과 새로운 timeout signal 결합 로직 필요  
      return await next();  
    } finally {  
      clearTimeout(timeoutId);  
    }  
  }  
}

### **2\. Error Mapping Behavior (Post-Processor 예시)**

TypeScript

export class ErrorMappingBehavior implements IPipelineBehavior {  
  async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
    const result \= await next();  
      
    if (\!result.success && ctx.metadata.schema \=== 'http') {  
      // 도메인 에러를 HTTP 상태 코드와 매핑하는 로직 수행  
      // 예: 'NOT\_FOUND' \-\> 404  
    }  
      
    return result;  
  }  
}

---

## **Ⅵ. 기대 효과 (KPI)**

1. **안정성(Reliability):** AbortSignal 전파를 통해 불필요한 연산 자원을 90% 이상 조기 회수.  
2. **가독성(Readability):** try-catch 지옥에서 벗어나 if (result.success) 형태의 깔끔한 비즈니스 흐름 구현.  
3. **확장성(Extensibility):** 신규 인프라(예: AWS Lambda) 도입 시 파이프라인은 그대로 두고 진입점(Entry)만 교체하여 즉시 대응.

---
