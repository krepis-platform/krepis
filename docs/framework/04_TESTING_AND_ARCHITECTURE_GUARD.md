# **📑 \[Krepis\] 3\. 검증: 아키텍처 가드 및 테스트 자동화 명세 (v1.5.0)**

버전: v1.5.0 (Deterministic Validation)

분류: 품질 보증, 아키텍처 가드 및 테스트 인프라

## **3.1 테스트 커버리지 및 강제성 (Sovereign Hard-Fail)**

* **임계치 및 통합 관리:** 모든 패키지의 테스트 커버리지는 **전 레이어 80% 이상**을 유지합니다.  
* **통합 리포팅:** Deno의 deno test \--coverage 결과와 Rust의 cargo-tarpaulin 리포트를 합산하여 최종 품질 지표를 산출합니다.  
* **CI Hard-Fail:** 단 1%라도 기준 미달 시 CI 파이프라인은 즉시 중단되며, 아키텍트의 수동 승인 없이는 배포 단계로 진입할 수 없습니다.

## **3.2 아키텍처 가드 및 결정적 순환 참조 (Zero-Cycle Guard)**

* **순환 참조 제로:** 모듈 및 패키지 간 순환 참조는 설계 결함으로 간주합니다. Deno 환경에 최적화된 종속성 분석 도구를 통해 감지 시 즉시 빌드를 중단합니다.  
* **Trinity 레이어 침범 탐지:** AST 기반 커스텀 린터가 **Domain → Application → Infrastructure**의 단방향 의존성을 상시 감시합니다. 특히 Domain 레이어에서 Deno 전역 객체나 외부 어댑터를 직접 참조하는 행위를 실시간 차단합니다.

## **3.3 인프라 및 네이티브 통합 테스트 (Environment Parity)**

* **네이티브 정합성 테스트:** TS 레이어는 \*\*Standard(Mock)\*\*와 **Turbo(Native FFI)** 두 가지 모드에서 동일한 테스트 스위트를 통과해야 합니다. 이는 네이티브 가속기(Rust) 도입 전후의 로직 일관성을 보장합니다.  
* **Infrastructure Test (Deno Testcontainers):** DB 및 Cache 연동 테스트 시 Mocking 대신 Testcontainers를 활용하여 실제 컨테이너 환경에서 검증합니다.  
* **Sovereign FFI Validation:** Rust에서 노출한 FFI 심볼이 TS 레이어의 기대 타입과 일치하는지 런타임 바인딩 체크를 수행합니다.

## **3.4 CI 가속 및 파이프라인 안정성 (Pipeline DX)**

* **Incremental Test Execution:** 변경된 파일과 직접적인 의존 관계에 있는 테스트 파일만 선별적으로 실행하여 CI 시간을 단축합니다.  
* **Deterministic Flaky Management:** 실패한 테스트는 최대 2회 재시도하되, 지속적으로 불안정한 테스트는 **'Quarantine'** 태그를 부여하여 별도 격리하고 아키텍처 개선 대상(Backlog)으로 즉시 등록합니다.

## **3.5 시각화 및 구조적 가시성 (Architecture Observability)**

* **Auto-generated Architecture Map:** 매 빌드 시 의존성 그래프를 SVG로 자동 생성하여 프로젝트 대시보드에 게시합니다.  
* **Complexity Monitoring:** 코드 복잡도가 임계치를 초과할 경우 AI Sentinel이 리팩토링을 제안하며, 특히 Application Service 레이어의 거대화를 방지합니다.

## **3.6 부트스트랩 무결성 검증 (Runtime Bootstrap Shield)**

* **Sovereign DI Validation:** 애플리케이션 기동 시 DI 컨테이너는 다음을 전수 검사합니다.  
  1. **Dependency Integrity:** 모든 Port에 대응하는 유효한 Adapter가 등록되었는가?  
  2. **Context Symmetry:** Rust 커널에서 요구하는 Context 구조가 TS 로직과 일치하는가?  
* **Fail-fast Startup:** 위 검증 실패 시 시스템은 실행을 거부하고 정확한 실패 지점과 해결 가이드를 출력합니다.

---

## **🛠️ 검증 시스템 구성 요약 (v1.5.0)**

| 항목 | 검증 도구 | 통제 방식 | 비고 |
| :---- | :---- | :---- | :---- |
| **커버리지** | deno test, cargo-tarpaulin | 80% 미만 CI 차단 | Rust/TS 통합 리포트 |
| **순환 참조** | deno\_graph 기반 분석 | 감지 시 즉시 빌드 중단 | 패키지/모듈 전체 감시 |
| **인프라 정합성** | Testcontainers (Docker) | 실제 컨테이너 연동 검증 | DB, Redis 실환경 테스트 |
| **이원화 검증** | Standard vs Turbo 대조 | 결과 불일치 시 패닉 | 네이티브 가속 정합성 확보 |
| **DI 무결성** | Krepis Core DI Engine | 런타임 기동 시 전수 검사 | 의존성 누락 및 타입 불일치 방지 |

---
