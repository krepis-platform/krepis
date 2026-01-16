# **📑 \[Krepis-Spec-014\] Unified Cache & Multi-Storage Module (v1.2.1)**

**버전:** v1.2.1 (Distributed L1 Sync & Stampede Protection 확장)

**상태:** Final Draft

**모듈명:** @krepis/cache

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Transparency & Consistency:** 로컬(L1)과 분산(L2) 캐시 간의 데이터 불일치를 실시간 메시징(Pub/Sub)으로 해결하여 최종 일관성을 보장합니다.  
2. **Infrastructure Resilience:** 캐시 엔진 장애 시 비즈니스 로직의 중단 없이 DB 직접 조회 또는 L1 Fallback으로 전환되는 탄력성을 가집니다.  
3. **Stampede Protection:** 동일 키에 대한 대규모 동시 요청 시, 단 하나의 요청만 원본 데이터를 조회하도록 제어하여 인프라 붕괴를 방지합니다.  
4. **Event-Driven Invalidation:** 명시적 삭제 코드 대신, 도메인 이벤트(Domain Events)와 연동하여 데이터 변경 시 캐시를 자동으로 폐기합니다.

---

## **Ⅱ. 핵심 아키텍처 및 인터페이스**

### **1\. 하이브리드 캐시 엔진 (L1-L2 Hybrid)**

로컬 메모리와 Redis를 단일 인터페이스로 묶어 관리합니다.

* **L1 (Local):** MemoryCacheProvider (최고 속도, 인스턴스별 격리)  
* **L2 (Distributed):** RedisCacheProvider (데이터 공유, 데이터 영속성)

### **2\. 분산 무효화 (Distributed Invalidation)**

서버 인스턴스가 여러 대일 때, 한 곳의 데이터 변경이 다른 서버의 L1 캐시를 즉시 비우도록 설계합니다.

TypeScript

export interface ICacheInvalidator {  
  /\*\* 전역적으로 특정 키의 L1 캐시를 무효화하도록 메시지 발행 (Redis Pub/Sub 활용) \*/  
  publishInvalidation(key: string): Promise\<void\>;  
  /\*\* 무효화 메시지 수신 시 로컬 메모리 비움 \*/  
  subscribeInvalidation(): void;  
}

---

## **Ⅲ. 상세 API 및 구현 전략**

### **1\. Single Flight (스탬피드 방지)**

동일한 키에 대한 getOrSet 요청이 몰릴 때, 최초 요청자만 실행하고 나머지는 결과를 공유받습니다.

TypeScript

export interface ICacheStore extends ICacheProvider {  
  /\*\* 원자적 조회 및 생성: 스탬피드 방지 로직 내장 \*/  
  getOrSet\<T\>(key: string, factory: () \=\> Promise\<T\>, options?: CacheOptions): Promise\<T\>;  
}

### **2\. 확장된 Cache Options**

TypeScript

export interface CacheOptions {  
  ttl: number;                // 만료 시간 (seconds)  
  sliding?: boolean;          // 접근 시마다 만료 시간 연장 여부  
  useL1?: boolean;            // L1 캐시 사용 여부  
  invalidationChannel?: string; // 무효화 공유 채널명  
}

---

## **Ⅳ. 도메인 이벤트 기반 무효화 (Integration)**

@krepis/core/events와 결합하여 데이터의 상태 변화와 캐시의 생명주기를 동기화합니다.

TypeScript

// application/handlers/ProductChangedHandler.ts  
export class ProductChangedHandler implements IDomainEventHandler\<ProductUpdatedEvent\> {  
  static inject \= \[ICacheManager\];  
  constructor(private cache: ICacheManager) {}

  async handle(event: ProductUpdatedEvent) {  
    const store \= this.cache.getStore('distributed');  
    const cacheKey \= \`product:${event.aggregateId}\`;  
      
    // 1\. L2(Redis) 데이터 삭제  
    await store.delete(cacheKey);  
    // 2\. 다른 모든 서버 인스턴스의 L1 캐시 무효화 전파  
    await store.publishInvalidation(cacheKey);  
  }  
}

---

## **Ⅴ. 데코레이터 및 AOP 확장 (Semantic Keys)**

인자값을 분석하여 가독성 있고 유일한 키를 생성합니다.

TypeScript

export class ProductService {  
  @Cacheable({   
    store: 'distributed',   
    ttl: 3600,   
    keyPrefix: 'product',  
    useL1: true // L1/L2 하이브리드 모드 활성화  
  })  
  async getProduct(productId: string) {  
    // 실제 DB 조회 로직  
    return await this.productRepo.findById(productId);  
  }  
}

---

## **Ⅵ. 기대 효과 (KPI)**

1. **네트워크 비용 절감:** L1 캐시 활성화를 통해 Redis(L2)로 향하는 트래픽을 최대 70\~80% 감소.  
2. **데이터 정확성:** 분산 무효화(Pub/Sub) 도입으로 멀티 인스턴스 환경에서의 데이터 불일치 이슈 0% 지향.  
3. **시스템 안정성:** Single Flight 메커니즘을 통해 DB Peak Load 상황에서도 캐시 만료로 인한 연쇄 장애(Cascading Failure) 차단.

---
