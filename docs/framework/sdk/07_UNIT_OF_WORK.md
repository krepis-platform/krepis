# **📑 \[Krepis-Spec-005\] Unit of Work (UoW) Specification (v1.1.0)**

**버전:** v1.1.0 (Transactional Outbox & Session Propagation)

**상태:** Final Draft

**모듈명:** @krepis/core/uow

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Atomic Integrity:** 여러 리포지토리의 작업과 도메인 이벤트 발행을 하나의 물리적 트랜잭션으로 묶어 "전부 성공 또는 전부 실패"를 보장합니다.  
2. **Infrastructure Agnostic:** 도메인 로직은 특정 DB의 트랜잭션 객체(Session, TransactionClient 등)를 직접 다루지 않습니다.  
3. **Exactly-once Event Delivery:** Transactional Outbox 패턴을 내장하여, DB 커밋이 성공했을 때만 이벤트가 외부로 발행되도록 보장합니다.  
4. **Implicit Context:** Context Propagation을 통해 트랜잭션 세션을 하위 리포지토리에 자동으로 전파하여 코드 오염을 방지합니다.

---

## **Ⅱ. 핵심 인터페이스 정의**

### **1\. IUnitOfWork (The Coordinator)**

트랜잭션의 생명주기와 세션 관리를 담당합니다.

TypeScript

* export interface IUnitOfWork {  
*   /\*\* 트랜잭션 시작 (내부적으로 DB 세션 생성 및 Context 바인딩) \*/  
*   start(): Promise\<void\>;  
*     
*   /\*\* \* 변경사항 확정 및 도메인 이벤트 발행   
*    \* 1\. DB 트랜잭션 커밋  
*    \* 2\. Outbox에 저장된 이벤트 발행 프로세스 트리거  
*    \*/  
*   commit(): Promise\<void\>;  
*     
*   /\*\* 모든 작업 취소 및 DB 세션 종료 \*/  
*   rollback(): Promise\<void\>;  
*   
*   /\*\* 현재 트랜잭션에 활성화된 원시 DB 클라이언트/세션 획득 (Adapter용) \*/  
*   getSession\<T\>(): T | undefined;  
* }

### **2\. IDomainEventDispatcher (Outbox Integration)**

UoW 내부에서 이벤트를 수집하고 처리하는 규격입니다.

TypeScript

* export interface IDomainEventDispatcher {  
*   /\*\* 엔티티로부터 수집된 이벤트를 Outbox 스토어에 임시 저장 \*/  
*   stageEvents(entities: AggregateRoot\[\]): void;  
*   /\*\* 커밋 성공 후 실제로 메시지 버스에 이벤트 전송 \*/  
*   dispatchStagedEvents(): Promise\<void\>;  
* }

---

## **Ⅲ. 실행 메커니즘: Implicit Session Propagation**

Krepis는 리포지토리 메서드에 세션을 인자로 넘기지 않습니다. 대신 **Context Proxy**를 사용합니다.

1. **Start:** TransactionBehavior가 uow.start()를 호출하면, UoW는 DB 세션을 생성하고 이를 @krepis/context의 현재 스토어에 TX\_SESSION\_KEY로 저장합니다.  
2. **Access:** 리포지토리는 인프라 레이어에서 context.get(TX\_SESSION\_KEY)를 통해 현재 활성화된 세션을 꺼내어 쿼리를 실행합니다.  
3. **End:** commit 또는 rollback 시점에 컨텍스트에서 세션 정보를 제거하고 자원을 해제합니다.

---

## **Ⅳ. 고도화된 Transactional Outbox (Implementation)**

DB 트랜잭션 내에 이벤트를 함께 저장하여 신뢰성을 확보합니다.

TypeScript

* // infrastructure/persistence/prisma/PrismaUnitOfWork.ts  
* export class PrismaUnitOfWork implements IUnitOfWork {  
*   async commit() {  
*     const session \= this.getSession\<Prisma.TransactionClient\>();  
*     const events \= this.eventDispatcher.getScopedEvents();  
*   
*     await session.$transaction(async (tx) \=\> {  
*       // 1\. 비즈니스 데이터 저장 (이미 리포지토리에 의해 수행됨)  
*         
*       // 2\. Outbox 테이블에 이벤트 기록 (동일 트랜잭션)  
*       await tx.outbox.createMany({  
*         data: events.map(e \=\> EventMapper.toOutbox(e))  
*       });  
*     });  
*   
*     // 3\. DB 커밋 성공 후, 즉시 브로커(Kafka/RabbitMQ)로 전송 시도 (Best Effort)  
*     await this.eventDispatcher.dispatchStagedEvents();  
*   }  
* }

---

## **Ⅴ. 통합 파이프라인 연동 (Final Flow)**

@krepis/pipeline과 결합된 트랜잭션 관리 전략입니다.

TypeScript

* export class TransactionBehavior implements IPipelineBehavior {  
*   static inject \= \[IUnitOfWork\];  
*   constructor(private readonly uow: IUnitOfWork) {}  
*   
*   async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
*     await this.uow.start();  
*   
*     try {  
*       const result \= await next();  
*   
*       // Result.success가 true인 경우에만 커밋  
*       if (result.success) {  
*         await this.uow.commit();  
*       } else {  
*         // 비즈니스 실패(예: 잔액 부족) 시 롤백하여 원자성 유지  
*         await this.uow.rollback();  
*       }  
*   
*       return result;  
*     } catch (error) {  
*       // 예외 발생 시 무조건 롤백  
*       await this.uow.rollback();  
*       throw error;  
*     }  
*   }  
* }

---

## **Ⅵ. 기대 효과 (KPI)**

1. **원자성(Atomicity):** 비즈니스 상태 변경과 이벤트 발행 간의 불일치 발생 확률 0%.  
2. **개발자 경험(DX):** 핸들러 코드에서 트랜잭션 관련 코드가 100% 제거됨.  
3. **신뢰성(Reliability):** 시스템 장애 시에도 Outbox에 저장된 이벤트를 통해 데이터 최종 일관성(Eventual Consistency) 회복 가능.

---
