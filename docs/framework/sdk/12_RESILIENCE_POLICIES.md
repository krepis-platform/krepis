# **📑 \[Krepis-Spec-008\] Resilience Policies Specification (v1.1.0)**

**버전:** v1.1.0 (Advanced Resilience & Policy Hierarchy)

**상태:** Final Draft

**모듈명:** @krepis/resilience

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Adaptive Self-Healing:** 장애 발생 시 자동으로 우회 경로를 찾고(Fallback), 일시적 오류는 지능형 재시도(Retry with Jitter)를 통해 스스로 복구합니다.  
2. **Resource Compartmentalization:** 벌크헤드(Bulkhead)를 통해 특정 서비스의 장애가 전체 시스템의 가용 자원(Thread/Memory)을 고갈시키지 않도록 격리합니다.  
3. **Holistic Protection:** 개별 정책이 아닌, 정책들이 중첩된 계층 구조(Policy Wrap)를 통해 다중 방어막을 형성합니다.  
4. **Result-Aware Logic:** 예외뿐만 아니라 Result.fail의 비즈니스 코드에 반응하여 정교한 탄력성 전략을 수행합니다.

---

## **Ⅱ. 정책 계층 구조 (Policy Hierarchy)**

복합 정책 적용 시 실행 순서를 정의하여 예측 가능한 동작을 보장합니다.

1. **Bulkhead (Outer):** 동시 실행 수를 제한하여 시스템 전체 자원을 보호.  
2. **Timeout:** 전체 실행 시간을 제한 (모든 재시도 시간을 포함하거나 개별 시도 제한).  
3. **Circuit Breaker:** 장애 전파를 차단하여 하위 서비스 부하 경감.  
4. **Retry (Inner):** 일시적 오류에 대해 재시도 수행.

---

## **Ⅲ. 핵심 정책 사양 확장**

### **1\. 지능형 재시도 (Retry with Full Jitter)**

동시에 재시도가 몰리는 'Thundering Herd' 현상을 방지합니다.

TypeScript

export interface IRetryOptions {  
  attempts: number;  
  backoff: {  
    type: 'exponential' | 'fixed';  
    baseDelay: number;  
    maxDelay: number;  
    useJitter: boolean; // 무작위 시간 추가로 충돌 방지  
  };  
}

// Jitter 계산 예시: delay \= random(0, min(cap, base \* 2^attempt))

### **2\. 벌크헤드 격리 (Bulkhead)**

특정 작업이 점유할 수 있는 최대 실행 큐와 동시성 제한을 설정합니다.

TypeScript

export interface IBulkheadOptions {  
  maxParallel: number;      // 최대 동시 실행 수  
  maxQueued: number;        // 대기 큐 크기  
  onFull: () \=\> Result\<any\>; // 큐가 가득 찼을 때의 즉시 응답  
}

---

## **Ⅳ. 상세 API 명세 (High-Level Builder)**

정책을 조합하여 하나의 거대한 방어막을 생성하는 인터페이스입니다.

TypeScript

// infrastructure/resilience/ResilienceProvider.ts  
const sharedPolicy \= Policy  
  .bulkhead(10, 20)          // 1\. 자원 격리  
  .timeout(5000)             // 2\. 전체 5초 제한  
  .circuitBreaker({          // 3\. 서킷 브레이커  
    failureThreshold: 0.5,  
    minimumThroughput: 10,  
    breakDuration: 30000  
  })  
  .retry({                   // 4\. 지능형 재시도  
    attempts: 3,  
    backoff: { type: 'exponential', baseDelay: 100, useJitter: true }  
  })  
  .fallback(DefaultValue);   // 5\. 최종 실패 시 대체값

---

## **Ⅴ. 분산 서킷 브레이커 (Distributed State)**

Redis 어댑터를 활용하여 인스턴스 간 장애 상태를 공유하는 메커니즘입니다.

TypeScript

export class DistributedCircuitBreaker implements IResiliencePolicy {  
  async execute\<T\>(action: () \=\> Promise\<Result\<T\>\>, ctx: IContextStore) {  
    const state \= await this.stateStore.getState(this.name);  
      
    if (state \=== 'OPEN') {  
      return Fail(new CircuitOpenError(this.name));  
    }

    const result \= await action();

    if (\!result.success && this.isFailure(result.error)) {  
      await this.stateStore.recordFailure(this.name);  
    }  
      
    return result;  
  }  
}

---

## **Ⅵ. 기대 효과 (KPI)**

1. **안정성(Reliability):** Jitter를 통한 재시도 분산으로 장애 복구 시 인프라 피크 부하 50% 감소.  
2. **격리성(Isolation):** 벌크헤드 적용으로 특정 API 장애 시 타 API 가용성 100% 유지.  
3. **가시성(Observability):** "서킷 오픈", "재시도 발생", "벌크헤드 거절" 등 모든 탄력성 이벤트가 traceId와 결합되어 모니터링 대시보드에 즉시 반영.

---
