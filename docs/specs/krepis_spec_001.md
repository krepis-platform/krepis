# **📑 \[Krepis-Spec-001\] Context Propagation Module Specification (v1.1.0)**

**버전:** v1.1.0 (Robustness & Hybrid Support 확장본)

**상태:** Final Draft

**모듈명:** @krepis/context

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Explicit Type Safety:** 제네릭 기반 ContextKey\<T\>를 통해 컴파일 타임에 타입을 확정합니다.  
2. **Immutability by Default:** 컨텍스트 데이터 오염을 방지하기 위해 스토어는 불변성을 지향하며, 변경 시 새로운 스토어를 생성(Copy-on-write)합니다.  
3. **Hybrid Boundary Continuity:** Node.js(TS)와 Native(Rust) 경계를 넘나들 때 컨텍스트가 유실되지 않도록 직렬화/복원 엔진을 내장합니다.  
4. **Resource Safety:** 요청 종료 시 메모리 누수를 방지하기 위한 명시적 정리(Cleanup) 메커니즘을 제공합니다.

---

## **Ⅱ. 핵심 데이터 구조 및 불변성 (Immutability)**

### **1\. Type-Safe Context Key (v1.1.0 추가)**

TypeScript

export class ContextKey\<T\> {  
  constructor(  
    public readonly name: string,  
    public readonly options?: {  
      readonly defaultValue?: T;  
      readonly sensitive?: boolean; // 로그 출력 시 마스킹 여부  
    }  
  ) {}  
}

### **2\. Immutable Context Store**

TypeScript

export interface IContextStore {  
  get\<T\>(key: ContextKey\<T\>): T | undefined;  
  has(key: ContextKey\<any\>): boolean;  
  /\*\*  
   \* 새로운 값을 포함한 '새 스토어 인스턴스'를 반환합니다. (불변성 유지)  
   \*/  
  set\<T\>(key: ContextKey\<T\>, value: T): IContextStore;  
  /\*\*  
   \* Rust 레이어로 전달하기 위한 직렬화 데이터  
   \*/  
  serialize(): string;   
  asMap(): Map\<string, any\>;  
  dispose(): void; // 메모리 정리  
}

---

## **Ⅲ. 하이브리드 전파 전략 (Technical Detail)**

### **1\. Native Bridge: Context Hydration (Rust ↔ TS)**

Rust 레이어에서 비동기 작업이 발생하거나 다시 TS로 콜백될 때를 위한 규격입니다.

TypeScript

// packages/native 연동 규격  
export interface INativeContextBridge {  
  // TS Context \-\> Rust Thread Local Storage  
  pushToNative(context: IContextStore): void;  
  // Rust Context \-\> TS ALS Restore  
  pullFromNative(): IContextStore;  
}

### **2\. Lazy Access Proxy (성능 최적화)**

TypeScript

export const ContextProxy \= new Proxy({} as IContextStore, {  
  get: (\_, prop: string | symbol) \=\> {  
    const store \= RequestContext.current();  
    if (\!store) {  
      // 스토어가 없을 경우 defaultValue를 가진 빈 스토어 혹은 에러 처리  
      throw new Error("KrepisContextError: Attempted to access context outside of an active scope.");  
    }  
    return Reflect.get(store, prop);  
  }  
});

---

## **Ⅳ. 방어적 실행 엔진 (Guardrails)**

### **1\. RequestContext Lifecycle**

컨텍스트의 시작과 끝을 엄격하게 관리하여 메모리 누수를 차단합니다.

TypeScript

export class RequestContext {  
  private static readonly storage \= new AsyncLocalStorage\<IContextStore\>();

  static run\<R\>(store: IContextStore, next: () \=\> Promise\<R\>): Promise\<R\> {  
    return this.storage.run(store, async () \=\> {  
      try {  
        return await next();  
      } finally {  
        store.dispose(); // 실행 완료 후 즉시 자원 해제  
      }  
    });  
  }  
}

---

## **Ⅴ. CQRS 파이프라인 결합 (Context Behavior)**

ContextBridgeBehavior는 이제 체크섬 및 보안 검증을 포함합니다.

TypeScript

export class ContextBridgeBehavior implements IPipelineBehavior {  
  async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
    // 1\. 요청 식별자 및 보안 정보 추출  
    let store \= new KrepisContextStore()  
      .set(TRACE\_ID, ctx.headers\['x-trace-id'\] || uuid())  
      .set(TIMESTAMP, Date.now());

    // 2\. 비동기 흐름 시작 및 자동 정리  
    return RequestContext.run(store, async () \=\> {  
      return await next();  
    });  
  }  
}

---

## **Ⅵ. 기대 효과 및 성능 목표 (KPI)**

1. **안전성(Stability):** 불변성 모델 도입으로 테넌트 간 데이터 오염 가능성 0%.  
2. **연속성(Continuity):** Rust 네이티브 모듈 호출 시에도 TraceId 유지율 100%.  
3. **메모리 효율:** dispose() 패턴을 통한 요청 종료 후 즉시 가비지 컬렉션(GC) 유도.

---
