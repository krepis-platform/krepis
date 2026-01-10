import { ContextFactory } from "../src/core/context/ContextFactory.ts";

/**
 * Krepis Kernel Advanced Stress Benchmark
 * 1. Heavy Payload: 대규모 메타데이터 처리 성능
 * 2. Parallel Burst: 수천 개의 컨텍스트 동시 생성 시 경합 확인
 * 3. Sequential Churn: 가비지 컬렉션 및 메모리 해제 효율 측정
 */

// [1] Heavy Payload 준비 (100개의 메타데이터 필드)
const heavyOptions = {
  tenantId: "enterprise-tenant-001",
  isTurboMode: true,
  metadata: Object.fromEntries(
    Array.from({ length: 100 }, (_, i) => [`custom_key_${i}`, `value_${Math.random()}`])
  ),
};

// [2] Parallel Burst (Promise.all 오버헤드 측정)
Deno.bench({
  name: "Context Parallel Burst (100 units)",
  group: "stress",
  async fn() {
    const tasks = Array.from({ length: 100 }, () => ContextFactory.create(heavyOptions));
    const contexts = await Promise.all(tasks);
    
    // 명시적 해제
    for (const ctx of contexts) {
      ctx[Symbol.dispose]();
    }
  },
});

// [3] Sequential Churn (1,000개 순차 생성 - 메모리 압박)
Deno.bench({
  name: "Sequential Churn (1,000 iterations)",
  group: "stress",
  fn() {
    for (let i = 0; i < 1000; i++) {
      using _ctx = ContextFactory.createSync(heavyOptions);
      // 루프 내부에서 즉시 해제되며 메모리 안정성 확인
    }
  },
});

// [4] FFI String Round-trip (데이터 무결성 및 변환 속도)
Deno.bench({
  name: "Metadata Round-trip Latency (Heavy)",
  group: "stress",
  fn() {
    using ctx = ContextFactory.createSync(heavyOptions);
    
    // 인터페이스의 getMetadata 메서드를 사용하여 실제 값을 조회합니다.
    // void 연산자로 호출을 평가하되 결과값은 무시하여 경고를 방지합니다.
    void ctx.getMetadata("custom_key_99");
  },
});

// [5] Full Metadata Extraction (전체 맵 변환 비용 측정)
Deno.bench({
  name: "All Metadata Retrieval Latency",
  group: "stress",
  fn() {
    using ctx = ContextFactory.createSync(heavyOptions);
    
    // getAllMetadata() 호출로 Protobuf 맵 전체를 JS 객체로 변환하는 비용 측정
    void ctx.getAllMetadata();
  },
});