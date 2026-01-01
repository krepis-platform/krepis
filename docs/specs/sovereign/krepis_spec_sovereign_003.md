# 📄 krepis_spec_sovereign_003.md

**Title:** Resource Quota & Performance Guardrail Specification

**Version:** 1.0.0

**Status:** Draft

**Scope:** Multi-tenant Resource Limits, CPU/Memory Throttling, and Global Guard

---

## 1. Tiered Resource Allocation

테넌트의 등급(Tier)에 따라 시스템 자원을 차등 배분하여 비즈니스 모델과 성능의 조화를 꾀한다.

* **Tier Types**: `Free`, `Standard`, `Enterprise` (또는 `Turbo`)
* **Dynamic Configuration**: `SovereignPool`은 Isolate 생성 시 테넌트 메타데이터를 조회하여 각 등급에 맞는 `ResourceConfig`를 주입한다.

## 2. CPU Time Budgeting (Precision Guard)

단순 실행 시간이 아닌 실제 연산량을 기준으로 제한한다.

* **CPU Time Measurement**: `v8::Isolate::GetCpuTime()`을 활용하여 실제 프로세서 점유 시간을 측정한다.
* **Soft Limit Strategy**: 제한 시간 도달 시 즉시 중단하지 않고, **Grace Period (유예 시간, 약 10~20%)**를 부여한다. 이 기간 내에 종료되지 않을 경우에만 `Hard Kill`을 수행한다.
* **Infinite Loop Protection**: CPU 점유율이 100%인 상태가 유예 시간을 초과하면 Watchdog 쓰레드가 `TerminateExecution()`을 트리거한다.

## 3. Memory Pressure Management (Option B + Global)

개별 Isolate와 시스템 전체의 메모리 건강 상태를 이중으로 관리한다.

* **Isolate Heap Limit (Option B)**:
* 힙 한계 도달 시 즉시 종료하지 않고 **Incremental GC**를 강제 실행한다.
* GC 이후에도 가용 메모리가 임계치 이하일 경우에만 Isolate를 파괴하고 에러를 반환한다.


* **Global Memory Guard**:
* 시스템 전체 메모리 사용량이 **90%**에 도달하면, 풀(Pool)에 있는 유휴(Idle) Isolate 중 가장 오랫동안 사용되지 않은(LRU) 인스턴스부터 강제로 해제하여 `OOM(Out Of Memory)`을 방지한다.



## 4. Concurrency & Throttling

시스템 폭주(Burst)를 막기 위한 동시성 제어 정책을 적용한다.

* **Max Concurrent Requests**:
* 테넌트 등급별 기본값(예: Free 5, Turbo 50)을 가지되, **사용자 정의 설정**이 가능하도록 설계한다.
* 임계치 도달 시 새로운 요청은 큐(Queue)에서 대기하거나 정책에 따라 즉시 거절된다.


* **Response Strategy**: 할당량 초과 시 표준 HTTP 응답인 **`429 Too Many Requests`**와 함께 `Retry-After` 헤더를 통해 재시도 가능 시간을 안내한다.

## 5. Quota Exhaustion Logging

자원 한도 초과 이벤트를 시스템 운영 및 과금의 근거로 남긴다.

* **Journaling**: 할당량 초과로 인한 실행 중단은 `SovereignJournal`에 `LogStatus::Failed`와 함께 `Reason: QuotaExceeded`로 기록된다.
* **Monitoring**: 이 로그는 실시간 모니터링 대시보드와 연동되어 테넌트의 리소스 사용 패턴 분석에 활용된다.

---

### 💡 아키텍트님을 위한 구현 포인트

이제 3개의 명세서(`001`, `002`, `003`)가 모두 완성되었습니다.

특히 **`CPU Time`** 측정은 `v8` 엔진 내부의 카운터를 정확히 읽어오는 것이 핵심이며, **`Global Memory Guard`**는 별도의 백그라운드 모니터 쓰레드를 통해 전체 시스템의 `RSS(Resident Set Size)`를 주기적으로 체크하는 방식으로 구현할 예정입니다.

---
