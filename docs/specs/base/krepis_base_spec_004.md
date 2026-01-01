# **📑 \[Krepis Base Spec-004\] 시스템 아키텍처 및 기술 스택 상세 명세서**

버전: v1.5.0 (The Robust Sovereign Infrastructure)

분류: 물리적 구조, 런타임 바인딩 및 CLI 워크플로우

## **1\. 하이브리드 통합 아키텍처 (Sovereign Monorepo)**

* **Unified Workspace:** **Cargo Workspaces**를 최상위 구조로 삼고, 그 하부에 Deno 기반의 TS 패키지들을 통합 관리합니다.  
* **Shared Schema (Protobuf & FFI Definition):** \* **KNUL Control Plane:** prost를 통해 Rust 통신 레이어의 타입을 정의합니다.  
  * **FFI Bridge Definition:** Rust와 TS 간의 메모리 레이아웃을 일치시키기 위해 정밀한 바인딩 명세를 공유하며, Deno의 FFI 선언부 코드를 자동 생성합니다.  
* **Directory Structure:**  
  * crates/krepis-kernel: Hyper-Pingora 기반 네이티브 서버 및 KNUL 엔진 (Rust)  
  * packages/core: Deno 기반의 Trinity 패턴 프레임워크 코어 (TS)  
  * packages/cli: Master CLI 엔진 (Rust) 및 아키텍처 검수 도구

---

## **2\. CLI 오케스트레이션 및 런타임 통제 (Sovereign Chain)**

* **Rust Master CLI:** 시스템에 설치된 **Deno 런타임**을 직접 제어합니다. Master CLI는 단순한 실행기가 아니라, TS 로직이 돌아가는 **Deno 프로세스의 부모(Watcher)** 역할을 수행하며 리소스 할당량을 감시합니다.  
* **Sandbox Isolation (V8 Isolates):** 각 명령 실행 시 Deno의 Worker API를 활용하여 독립된 **V8 Isolate** 환경을 제공합니다. 이는 플러그인의 오류나 악성 로직이 전체 시스템(Rust Kernel)의 패닉으로 이어지는 것을 물리적으로 차단합니다.  
* **Transactional File System (Sled Log):** CLI를 통한 모든 AST 조작 전, sled DB에 원본 파일의 스냅샷과 Diff를 기록합니다. krepis undo 명령 시 네이티브 레벨에서 파일 시스템 복구를 수행합니다.

---

## **3\. Smart Generator 및 패키지 시스템 (Generator & Marketplace)**

* **Deep AST Manipulation (Explicit Context Ready):** ts-morph를 활용하여 코드를 생성할 때, 모든 비동기 함수에 **ctx: KrepisContext** 인자가 누락되지 않도록 강제 주입합니다. 아키텍처 규칙 위반 시 생성 단계에서 Rust 커널이 빌드를 거부합니다.  
* **Krepis Package (.kpkg):** TS 소스코드와 함께, 특정 OS에서 성능 가속이 필요한 경우 최적화된 **Rust WebAssembly(Wasm)** 또는 **네이티브 바이너리**를 포함한 단일 포맷입니다.  
* **Deno-Native Dependency Management:** krepis add로 추가된 모듈은 Deno의 캐시 메커니즘을 활용하여 관리되며, 프로젝트 로컬의 .krepis/modules 폴더에 버전별로 고립 저장됩니다.

---

## **4\. 고성능 바인딩 및 런타임 배포 (Deno FFI & Delivery)**

* **Dynamic FFI Loading:** 사용자는 Rust를 몰라도 됩니다. Krepis 설치 시 운영체제에 맞는 \*\*Sovereign Core 바이너리(.so, .dll, .dylib)\*\*가 자동 다운로드됩니다.  
* **Zero-Overhead Bridge:** Deno의 \*\*FFI(Foreign Function Interface)\*\*를 사용하여 Rust의 네이티브 함수를 직접 호출합니다.  
  * **Fast Call:** 간단한 연산은 Fast Call 옵션을 통해 오버헤드를 최소화합니다.  
  * **Shared Memory:** 대용량 KNUL 패킷은 SharedArrayBuffer를 통해 Rust 메모리 주소를 TS가 직접 들여다보는 방식으로 처리합니다.

---

## **5\. 로컬 데이터 인프라 (Sled DB & OS Keychain)**

* **Sled DB 역할:**  
  * **Caching:** AST 분석 결과 및 모듈 인덱싱 정보를 네이티브 성능으로 저장/조회합니다.  
  * **Shadow Metrics:** 섀도우 테스팅에서 수집된 성능 지표를 로컬에 축적하여 AI의 피드백 루프 데이터로 제공합니다.  
* **Hardware-Level Security:** 인증 토큰과 비즈니스 로직 보호를 위한 마스터 키는 OS의 **Keychain/Secret Service**와 연동하여 AES-256-GCM으로 암호화합니다.

---

## **6\. 서드파티 플러그인 거버넌스 (Sovereign Governance)**

* **Strict Validation Pipeline:** 모든 플러그인은 마켓플레이스 등록 전 반드시 검수 과정을 거칩니다.  
  * **Static Analysis:** Deno의 권한 시스템(Permission System)을 활용하여 플러그인이 허가되지 않은 파일 시스템/네트워크 접근을 시도하는지 정밀 검사합니다.  
  * **AI Sentinel Integration:** \[Spec-003\]의 AI 클러스터가 플러그인의 Explicit Context 사용 방식을 분석하여 데이터 유출 위험을 리포팅합니다.  
* **Digital Signature:** 검수를 통과한 플러그인에 한해 네이티브 서명이 부여되며, 실행 시 Rust 커널이 서명을 대조하여 무결성을 확인합니다.

---

## **7\. 핵심 가치 요약 (The Infrastructure Pillars v1.5.0)**

| 가치 | 설명 | 기술적 실현 |
| :---- | :---- | :---- |
| **Runtime Sovereignty** | 런타임에 대한 완전한 통제권 | Rust Master CLI \+ Deno Process 제어 |
| **Zero-copy I/O** | 데이터 복사 없는 초고속 성능 | Deno FFI \+ Shared Memory 포인터 |
| **Isolation & Safety** | 플러그인 및 태스크의 완벽 고립 | V8 Isolates \+ Rust Kernel Guard |
| **Atomic Updates** | 안정적인 아키텍처 변경 및 복구 | Sled 기반 Transactional Log 시스템 |

---
