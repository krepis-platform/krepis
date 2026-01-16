# **📑 \[Krepis Base Spec-001\] 프로젝트 비전 및 하이브리드 철학 상세 명세서**

버전: v1.5.0 (The Deterministic Sovereign)

분류: 핵심 전략 및 아키텍처 원칙

## **1\. 서비스 정의: ADaaS (Architecture Development as a Service)**

Krepis는 소프트웨어의 생애주기(SDLC) 전체를 자율적으로 관리하는 **'아키텍처 자율 주행' 플랫폼**입니다. 단순한 코드 생성을 넘어, **결정적(Deterministic) 런타임** 위에서 구조적 무결성을 유지하고 스스로 진화하는 시스템을 지향합니다.

### **1.1 자율 주행 매커니즘 (Autonomous Operation)**

* **초결정적 데이터 분석 (Deterministic Insight):** Deno와 Rust 네이티브 레이어를 통해 런타임의 모든 요청과 응답, 비동기 호출 흐름을 **명시적 컨텍스트(Explicit Context)** 단위로 실시간 인덱싱합니다.  
* **섀도우 테스팅 및 검증 (Shadow Testing):** AI가 제안한 신규 코드는 Rust 기반의 **Smart Dispatcher**를 통해 실제 트래픽의 일부와 대조 검증됩니다. 논리적 정합성 및 성능 지표가 임계치를 통과해야만 머지 대상이 됩니다.  
* **지능형 PR 및 인간 승인 (Human-in-the-loop):** 검증을 마친 AI는 변경 이력과 성능 리포트를 포함한 PR을 생성하며, 인간 아키텍트는 승인 버튼 하나로 자동 배포를 완료합니다.

### **1.2 사용자 페르소나별 가치 (Target Value)**

* **Junior Devs (Architectural Education):** 명시적 컨텍스트 주입 패턴을 통해 데이터의 흐름을 시각적으로 이해하고, 헥사고날 패턴의 규칙 위반 시 Rust 커널이 제공하는 즉각적인 피드백을 통해 성장합니다.  
* **Senior Architects (Operational Excellence):** Hyper-Pingora 엔진이 인프라 레벨의 복잡성을 흡수하여, 시니어는 오직 고수준 비즈니스 도메인 설계와 전략 수립에만 집중합니다.

---

## **2\. 하이브리드 엔진 철학 (The Sovereign-Core Strategy)**

Krepis는 성능과 지능의 결합을 위해 \*\*Rust 네이티브 통치(Sovereign)\*\*와 **TypeScript 비즈니스 로직**을 결합한 독보적 구조를 채택합니다.

### **2.1 런타임 및 엔진 통합 (Unified Sovereign Engine)**

* **Deno Runtime:** Node.js의 불확실한 비동기 전파를 탈피하고, Deno의 엄격한 리소스 관리와 고성능 FFI를 기본 실행 환경으로 채택합니다.  
* **Hyper-Pingora Engine:** 외부 프레임워크(Express 등) 의존성을 제거하고, Rust 네이티브 기반의 고성능 네트워크 스택을 직접 탑재합니다.  
  * **Inbound/Outbound:** Hyper를 통한 초고속 패킷 처리.  
  * **Infrastructure Logic:** Pingora에서 영감을 얻은 커넥션 풀링 및 제로 다운타임 로직 내장.

### **2.2 명시적 컨텍스트와 결정성 (Explicit Context & Bridge)**

* **Explicit Context Injection:** AsyncLocalStorage와 같은 마법을 배제합니다. 모든 비동기 호출은 Rust 커널이 생성한 **ctx 객체를 인자로 명시적으로 전달**받아 실행됩니다. 이는 AI가 코드의 인과관계를 100% 파악하게 만드는 핵심 기치입니다.  
* **Zero-copy FFI Bridge:** Rust 레이어에서 받은 요청 데이터를 Deno/TS로 넘길 때 메모리 복사 없이 포인터와 공유 버퍼를 활용하여 I/O 병목을 근본적으로 제거합니다.  
* **Resource Guard & Isolation:** TS 로직에서 발생하는 오류나 무한 루프는 Rust 커널이 실시간 감시하며, 위반 시 해당 컨텍스트 핸들만 네이티브 레벨에서 강제 종료하여 시스템 전체의 안정성을 보장합니다.

---

## **3\. 아키텍처 제약 및 독립성 정책**

### **3.1 강제된 Trinity 패턴 (Hard-Constrained Trinity)**

Krepis는 AI 최적화를 위해 다음 세 가지 패턴의 조합을 강제합니다.

* **Hexagonal (외벽):** 어댑터 분리를 통한 외부 의존성 격리.  
* **Functional Core (심장):** 순수 함수 기반의 비즈니스 로직 구성을 통한 AI 검증 극대화.  
* **CQS (작동):** 명확한 명령과 조회 분리로 데이터 무결성 확보.  
* **제약 수단:** AST 분석 엔진이 빌드 타임에 계층 침범을 감지하면 강력한 컴파일 에러를 발생시킵니다.

### **3.2 탈출 전략 및 자산 보존 (No Lock-in Policy)**

* **표준 기반 코드 추출:** 사용자가 플랫폼을 떠나더라도 명시적 컨텍스트 주입 기반의 순수 TS 로직은 보존됩니다.  
* **환경 이식성:** Krepis의 표준 인터페이스는 타 프레임워크로의 전환이 용이하도록 설계되었으며, 필요시 바닐라 TS 코드로 변환해 주는 전용 Export 기능을 제공합니다.

---

## **4\. 핵심 가치 요약 (The Krepis Pillars v1.5.0)**

| 가치 | 설명 | 기술적 실현 |
| :---- | :---- | :---- |
| **Hyper Determinism** | 런타임 유실 없는 완벽한 결정성 | Rust 네이티브 컨텍스트 생성 및 명시적 주입 |
| **Sovereign Power** | 엔터프라이즈급 초고성능 제공 | Hyper-Pingora 하이브리드 엔진 내장 |
| **AI-Native Flow** | AI가 100% 이해하는 코드 구조 | Trinity 패턴 및 Explicit Context 강제 |
| **KNUL Connectivity** | 초연결 차세대 통신 표준 | Rust 네이티브 기반 KNUL 프로토콜 통합 |

---