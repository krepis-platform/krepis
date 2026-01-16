# **📑 \[Krepis-Spec-007\] Domain Events Module Specification (v1.1.0)**

**버전:** v1.1.0 (Reliability & Evolution 확장)

**상태:** Final Draft

**모듈명:** @krepis/core/events

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Observability by Design:** 모든 이벤트는 발생 시점의 실행 문맥(Trace, User, Tenant)을 강제로 포함하여 시스템 전반의 인과 관계를 추적합니다.  
2. **Reliable Delivery:** Transactional Outbox와 결합하여 "DB 커밋 시 이벤트 발행"을 보장하며, 실패 시 재시도 메커니즘을 내장합니다.  
3. **Strict Ordering:** 동일 애그리거트 내의 이벤트는 발생 순서대로 처리됨을 보장하여 상태 불일치를 방지합니다.  
4. **Schema Evolution Ready:** 이벤트 버전 관리와 업캐스팅(Upcasting)을 지원하여 시스템 성장에 따른 하이브리드 버전 호환성을 유지합니다.

---

## **Ⅱ. 핵심 데이터 구조 및 메타데이터**

### **1\. 고도화된 IEventMetadata**

순서와 버전을 제어하기 위한 필드가 추가되었습니다.

TypeScript

export interface IEventMetadata {  
  readonly eventId: string;        // 고유 이벤트 ID (멱등성 체크용)  
  readonly aggregateId: string;    // 대상 애그리거트 ID (순서 보장 파티셔닝 키)  
  readonly sequence: number;       // 애그리거트 내 발생 순서  
  readonly version: number;        // 이벤트 스키마 버전  
  readonly occurredAt: Date;  
  readonly correlationId: string;  // TraceId  
  readonly userId?: string;  
}

### **2\. IDomainEvent 베이스 클래스**

TypeScript

export abstract class IDomainEvent {  
  // 이벤트 클래스 이름을 상속받아 타입을 식별 (예: "UserRegistered")  
  public abstract readonly eventType: string;  
  public metadata?: IEventMetadata;  
}

---

## **Ⅲ. 신뢰성 및 정합성 엔진 (The Reliability Engine)**

### **1\. 멱등성 보장 (Idempotent Consumer)**

핸들러 수준에서 중복 처리를 방지하기 위한 가드레일입니다.

TypeScript

export abstract class IdempotentHandler\<T extends IDomainEvent\> {  
  async handle(event: T): Promise\<void\> {  
    const { eventId } \= event.metadata\!;  
      
    // 이미 처리된 이벤트인지 확인 (Redis 또는 DB 기반)  
    if (await this.isAlreadyProcessed(eventId)) return;

    await this.process(event);  
    await this.markAsProcessed(eventId);  
  }

  protected abstract process(event: T): Promise\<void\>;  
}

### **2\. 이벤트 업캐스팅 (Schema Evolution)**

구버전 이벤트를 현재 버전의 핸들러가 처리할 수 있도록 변환합니다.

TypeScript

export interface IEventUpcaster {  
  readonly eventType: string;  
  readonly fromVersion: number;  
  upcast(rawPayload: any): any; // 구버전 데이터를 신버전 규격으로 변환  
}

---

## **Ⅳ. 실행 및 디스패칭 전략**

### **1\. Execution Mode & Priority**

핸들러 등록 시 실행 우선순위와 동기/비동기 여부를 결정합니다.

TypeScript

export enum EventPriority {  
  CRITICAL \= 0, // 캐시 갱신 등 즉시 반영 필요  
  NORMAL \= 1,   // 로깅, 알림 등  
  LOW \= 2       // 통계 데이터 수집 등  
}

export interface IEventHandlerOptions {  
  readonly async: boolean;  
  readonly priority: EventPriority;  
  readonly retryCount?: number; // 비동기 실패 시 재시도 횟수  
}

### **2\. Outbox & Background Dispatcher**

비동기 이벤트는 EventOutbox를 거쳐 안전하게 발행됩니다.

TypeScript

export class BackgroundDispatcher {  
  async dispatch(events: IDomainEvent\[\]) {  
    // 1\. 순서 보장을 위해 aggregateId 기반으로 그룹화  
    // 2\. 외부 브로커(Kafka/RabbitMQ)의 파티션 키로 aggregateId 사용  
    // 3\. 전송 실패 시 Dead Letter Queue(DLQ)로 이동  
  }  
}

---

## **Ⅴ. 구현 및 사용 예시**

TypeScript

// 유저 이메일 변경 이벤트 (v2)  
export class UserEmailChangedEvent extends IDomainEvent {  
  readonly eventType \= "UserEmailChanged";  
  constructor(  
    public readonly oldEmail: string,   
    public readonly newEmail: string  
  ) { super(); }  
}

// 애그리거트 내부에서의 발생  
user.changeEmail("new@krepis.io"); // 내부에서 raiseEvent 호출 시 sequence 자동 증가

---

## **Ⅵ. 기대 효과 (KPI)**

1. **데이터 무결성:** sequence 기반 순서 보장과 version 기반 업캐스팅으로 데이터 정합성 100% 유지.  
2. **시스템 탄력성:** 비동기 재시도 및 DLQ 전략을 통해 외부 시스템 장애 시에도 이벤트 유실 0%.  
3. **운영 효율:** 모든 이벤트에 박힌 correlationId를 통해 마이크로서비스 간 분산 트레이싱 가시성 확보.

---
