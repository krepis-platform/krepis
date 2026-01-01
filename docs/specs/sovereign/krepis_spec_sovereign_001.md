# 📄 krepis_spec_sovereign_001.md

**Title:** Runtime Isolation & Isolate Pooling Specification

**Version:** 1.0.0

**Status:** Draft

**Scope:** V8 Isolate Management and Multi-tenant Execution Boundary

---

## 1. Isolate Pooling (Pingora-style)

Pingora의 디자인 철학을 따라, **"Warm-start"**를 지향하는 **LRU(Least Recently Used) 기반 테넌트 풀링**을 채택한다.

* **Warm Isolate Pool**: 요청마다 Isolate를 파괴하지 않고, `tenant_id`를 키로 하여 일정 시간 동안 메모리에 유지한다.
* **Dynamic Scaling**: 활성 요청이 많을 경우 풀의 크기를 동적으로 확장하며, 유휴 상태가 길어지는 Isolate는 Pingora의 커넥션 풀링처럼 우아하게(Gracefully) 폐기한다.

## 2. State Reset & Execution Strategy

효율성을 위해 **"Fresh Context per Request"** 전략을 사용한다.

* **Isolate Reuse, Context Refresh**: 무거운 `v8::Isolate`(엔진 인스턴스)는 재사용하되, 요청이 들어올 때마다 `v8::Context`(글로벌 스코프)를 새로 생성한다.
* **Zero-Contamination**: 이를 통해 이전 요청의 전역 변수 오염을 완벽히 차단하면서도, Isolate 생성에 드는 수 밀리초(ms)의 오버헤드를 절약한다.

## 3. Resource & Performance Limits (The "Golden Standard")

V8의 가장 일반적이고 효율적인 리소스 제한 수치를 적용한다.

* **V8 Heap Limits**: 테넌트당 **128MB ~ 256MB**를 Soft limit으로 설정한다. (대규모 데이터 처리가 없는 일반적인 서버리스 워크로드의 표준)
* **Termination Strategy**: 힙 한도 도달 시 `NearHeapLimitCallback`을 통해 1차 GC를 시도하고, 이후에도 메모리 부족 시 해당 Isolate만 즉시 폐기(Terminate)하여 호스트(Kernel)를 보호한다.

## 4. Execution Guard (Watchdog)

무한 루프 및 CPU 독점 방지를 위해 **Interrupt-based Watchdog**을 구현한다.

* **Execution Deadline**: 단일 요청의 최대 실행 시간은 **50ms ~ 100ms**로 제한한다. (Real-time responsiveness 확보)
* **Infinite Loop Protection**: `v8::Isolate::TerminateExecution()`을 호출하는 별도의 Watchdog 쓰레드를 운영하여, 메인 이벤트 루프를 차단하는 악성 코드를 강제 중단시킨다.

## 5. Operation & Fault Isolation

* **Shared vs Private Ops**: `deno_core`의 `Extension` 시스템을 통해 **Shared Core Ops**(Logging, Stats)는 공통으로 제공하되, 테넌트 등급에 따라 **Namespace-restricted Ops**(파일 접근 권한 등)를 동적으로 필터링하여 노출한다.
* **Isolation Boundary**: 각 Isolate 실행은 `std::panic::catch_unwind` 영역 내에서 관리된다. 특정 테넌트의 코드가 네이티브 패닉을 유도하더라도, 커널 메인 쓰레드는 생존하며 해당 테넌트의 풀 인스턴스만 교체한다.

---