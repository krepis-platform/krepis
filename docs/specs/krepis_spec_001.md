# 📑 

 Context Propagation Module Specification (v1.2.0)

**버전:** v1.2.0 (Native-First & Explicit Injection 통합본)

**상태:** Final Draft

**모듈명:** @krepis/context

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Explicit Over Implicit:** `AsyncLocalStorage`와 같은 암시적 저장소를 배제하고, 모든 함수와 DI 컴포넌트는 `ctx`를 인자로 명시적으로 전달받습니다.
2. **Native-Origin Truth:** 컨텍스트의 생성 주체는 항상 **Rust Sovereign Kernel**이며, TS 레이어는 이를 고성능 바이너리(Protobuf) 형태로 소비합니다.
3. **Zero-Inertia Propagation:** 컨텍스트는 단순한 데이터 묶음이 아니라, 리소스 쿼터(Quota)와 실행 권한을 담은 '통치권(Sovereignty)'의 증명입니다.
4. **Disposable Lifecycle:** 컨텍스트는 `using` 구문과 결합하여 실행 종료 시 즉시 커널 메모리에서 해제됩니다.

---

## **Ⅱ. 핵심 데이터 구조 (Native-Integrated)**

### **1. Sovereign Context Wrapper**

커널에서 넘어온 Protobuf 바이너리를 래핑하며, `Symbol.dispose`를 통해 브릿지 메모리를 관리합니다.

```typescript
export interface IKrepisContext extends Disposable {
  readonly requestId: string;
  readonly tenantId: string;
  readonly traceId: string;
  readonly isTurboMode: boolean;
  readonly timestamp: bigint;
  
  // 브릿지 통신을 위한 로우 바이너리 접근
  readonly binary: Uint8Array;
  
  // 커스텀 메타데이터 접근
  getMetadata(key: string): string | undefined;
}

```

### **2. Explicitly Injected DI Container**

모든 서비스는 생성자나 메서드 호출 시 `ctx`를 명시적으로 요구하도록 인터페이스를 강제합니다.

```typescript
// DI 관리 인터페이스 예시
export interface IScopedService {
  execute(ctx: IKrepisContext, ...args: any[]): Promise<any>;
}

```

---

## **Ⅲ. 하이브리드 전파 전략 (Technical Detail)**

### **1. Bridge Layer: Context Hand-off**

`AsyncLocalStorage`를 사용하지 않으므로, 커널과 SDK 사이의 컨텍스트 동기화는 **'명시적 핸드오프'** 방식으로 이루어집니다.

```typescript
// [Spec-Dev-002] Sovereign Bridge 연동 규격
export class SovereignContextBridge {
  /**
   * 커널로부터 새로운 컨텍스트를 생성하여 가져옵니다.
   */
  static async create(tenantId: string, options: ContextOptions): Promise<IKrepisContext> {
    const buffer = kernel.create_context(tenantId, options);
    return new KrepisContext(buffer); // 내부에서 FfiBuffer 관리
  }
}

```

### **2. Functional Propagation Pattern**

비즈니스 로직은 다음과 같은 파이프라인 패턴을 따릅니다.

```typescript
// ❌ 기존 방식 (Implicit)
// const traceId = RequestContext.current().traceId;

// ✅ 수정 방식 (Explicit)
async function handleRequest(ctx: IKrepisContext, input: any) {
  const result = await userService.findUser(ctx, input.userId);
  return result;
}

```

---

## **Ⅳ. 리소스 및 보안 거버넌스 (Guardrails)**

### **1. Lifetime Guard (using Pattern)**

커널 메모리 누수를 방지하기 위해 컨텍스트의 생명주기를 언어 레벨에서 강제합니다.

```typescript
// Controller 레이어 예시
async function onHttpRequest(req: Request) {
  // 블록을 벗어나는 순간 커널의 free_buffer가 자동 호출됨
  using ctx = await SovereignContextBridge.create(req.tenantId, { isTurbo: true });
  
  return await app.dispatch(ctx, req.body);
}

```

### **2. Deterministic Traceability**

* 모든 로그와 저널링(`SovereignJournal`)은 인자로 받은 `ctx.traceId`를 기반으로 기록됩니다.
* `ctx`가 없는 연산은 '신뢰할 수 없는 연산'으로 간주하여 커널 레이어에서 차단됩니다.

---

## **Ⅴ. CQRS 파이프라인 결합 (Updated Context Behavior)**

파이프라인은 더 이상 `storage.run()`을 호출하지 않고, `ctx` 객체를 생성하여 다음 파이프로 **'주입'**합니다.

```typescript
export class ContextBridgeBehavior implements IPipelineBehavior {
  async handle(req: RawRequest, next: NextPipe<any>) {
    // 1. 커널을 통한 컨텍스트 생성 (Native Bridge 호출)
    using ctx = await SovereignContextBridge.fromRequest(req);

    // 2. 하위 로직에 명시적으로 주입
    return await next(ctx);
  }
}

```

---

## **Ⅵ. 기대 효과 및 성능 목표 (KPI)**

1. **초결정성(Determinism):** 컨텍스트가 인자로 명시됨으로써 AI가 코드의 인과관계를 100% 추적 가능.
2. **제로 메모리 릭:** `AsyncLocalStorage`의 가비지 컬렉션 의존성을 탈피, `using` 구문으로 커널 메모리 즉시 회수.
3. **성능 우위:** 스레드 로컬 스토리지 조회 오버헤드 제거 (Direct Reference Access).

---