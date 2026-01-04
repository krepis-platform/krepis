import { ContextFactory } from "./ContextFactory.ts";

/**
 * Krepis SDK Context Lifecycle Benchmark
 * * 실행 방법:
 * deno bench --allow-ffi --allow-read src/core/context/context_bench.ts
 */

// 1. Mock Data 준비
const mockOptions = {
  tenantId: "benchmark-tenant",
  isTurboMode: true,
  priority: 10,
  metadata: {
    region: "ap-northeast-2",
    env: "production",
    version: "1.0.0"
  }
};

Deno.bench({
  name: "Context Creation (Async/FFI)",
  group: "lifecycle",
  baseline: true,
  async fn() {
    using ctx = await ContextFactory.create(mockOptions);
    if (ctx.tenantId !== "benchmark-tenant") throw new Error("Validation failed");
  },
});

Deno.bench({
  name: "Context Creation (Sync/FFI Fast-path)",
  group: "lifecycle",
  fn() {
    using ctx = ContextFactory.createSync(mockOptions);
    if (ctx.tenantId !== "benchmark-tenant") throw new Error("Validation failed");
  },
});

// 벤치마크 파일 상단에 정의
const sink = (_unused: unknown) => {};

Deno.bench({
  name: "Context Property Access (Warm Cache)",
  group: "access",
  fn() {
    using ctx = ContextFactory.createSync(mockOptions);
    for (let i = 0; i < 100; i++) {
      sink(ctx.requestId);
      sink(ctx.tenantId);
      sink(ctx.traceId);
    }
  },
});

Deno.bench({
  name: "Raw Protobuf Encoding Only",
  group: "serialization",
  fn() {
    // SovereignContext 내부에 숨겨진 인코딩 로직만 별도 측정
    // (이 부분은 SovereignContext.ts에서 export되어 있어야 합니다)
    // @ts-ignore: Internal helper access
    import("./SovereignContext.ts").then(m => m.encodeContextOptions(mockOptions));
  },
});