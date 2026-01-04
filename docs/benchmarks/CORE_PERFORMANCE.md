# Krepis Core Performance Report

## Environment

* **CPU**: AMD EPYC 7763 64-Core Processor
* **Runtime**: Deno 2.6.3 (x86_64-unknown-linux-gnu)
* **Kernel**: Krepis Rust Kernel v0.1.0 (FFI)

## Performance Metrics

| Component | Metric | Average Latency | Ops/sec | Notes |
| --- | --- | --- | --- | --- |
| **DI Singleton** | Resolve | **14.0 ns** | 71.5M | V8 Fast-path Inlined |
| **DI Scoped** | Resolve (Cached) | 500.8 ns | 1.9M | Warm Scope Cache |
| **Context** | Create (Sync) | 4.1 µs | 243K | Base Overhead |
| **Context (Heavy)** | Metadata (100 fields) | **968.2 µs** | 1.0K | Full Lifecycle |
| **Serialization** | Protobuf Encode | 3.2 µs | 313K | Rust-side logic |

## Stress Test Results & Analysis

* **Singleton Near-Zero Overhead**: 14ns는 DI 컨테이너가 런타임 오버헤드 없이 정적 코드에 가까운 속도로 동작함을 증명합니다.
* **FFI Efficiency**: 컨텍스트 생성 시 순수 인코딩 대비 추가 비용이 0.9µs에 불과하여, Rust-JS 경계가 매우 얇게 유지되고 있습니다.
* **Scalability Paradox**: 메타데이터 100개 포함 시 지연시간이 1ms 수준으로 선형 증가하며, 병렬 처리(Parallel Burst) 시 대기열 발생으로 인해 지연이 누적되는 현상을 확인했습니다.

---

## 🏗️ Future Optimization Roadmaps (The Next Frontier)

스트레스 테스트에서 발견된 성능 저하 요인을 해결하기 위한 아키텍처적 대응 과제입니다.

### **1. Metadata Allocation Optimization (Anti-GC Churn)**

* **Issue**: 대규모 메타데이터 생성 시 V8의 Young Generation 힙 부하 급증 및 가비지 컬렉션(GC) 개입 발생.
* **Solution**: **Object Pooling** 기술을 도입하여 빈번한 컨텍스트 생성/파괴 시 메모리 재할당을 최소화하고, 재사용 가능한 버퍼 구조를 설계할 예정입니다.

### **2. Shared Memory Context (Zero-Copy Strategy)**

* **Issue**: FFI 경계를 넘을 때 발생하는 데이터 복사(Copy) 비용이 헤비 페이로드에서 병목으로 작용.
* **Solution**: **SharedArrayBuffer** 또는 **Shared Memory**를 활용하여 Rust와 JS가 동일한 메모리 주소를 공유, 직렬화/역직렬화 오버헤드를 물리적으로 제거하는 아키텍처를 검토 중입니다.

### **3. FFI Fast-call Lane**

* **Issue**: 대량의 동시 FFI 호출 시 시스템 콜 레벨의 경합(Contention) 발생.
* **Solution**: Deno의 `Fast-API` 최적화를 적극 활용하고, 커널 명령을 배치(Batch) 처리하는 전용 레인을 구축하여 처리량(Throughput)을 Go 네이티브 수준으로 견인할 것입니다.

---