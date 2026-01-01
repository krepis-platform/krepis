# **📑 \[Krepis dev spec README\] 개발 환경 및 품질 관리 표준 명세서 (v1.5.0)**

문서 번호: KRP-STD-2025-001-REV1.5

대상을: 모든 크레이트(crates/), 패키지(packages/), 도구(tools/\*)

핵심 가치: Sovereign 통합(Unified), 빌드 결정성(Determinism), 아키텍처 강제(Enforcement)

---

## **1\. 뼈대: Sovereign 통합 빌드 파이프라인**

Krepis는 Deno와 Rust라는 두 개의 강력한 생태계를 단일 워크플로우로 통합합니다. 외부 오케스트레이터(Turborepo 등)에 의존하지 않고, **Deno Task**와 **Cargo**의 네이티브 기능을 결합합니다.

### **\[1.1\] 작업(Task) 및 오케스트레이션**

모든 컴포넌트는 언어와 관계없이 다음 표준 태스크를 준수하며, deno task를 통해 호출됩니다.

* **check**: Rust(clippy) 및 TS(deno check)의 정적 분석 및 타입 검사.  
* **test**: 네이티브 유닛 테스트 및 통합 테스트 실행.  
* **build**: Rust 바이너리 컴파일 및 Deno 런타임 최적화.  
* **dev**: Standard 모드(TS Simulator) 기반의 핫 리로딩 개발 환경.

### **\[1.2\] 하이브리드 의존성 전파 규칙**

* **Native First**: crates/krepis-kernel의 변경은 packages/core 빌드에 즉각 반영되어야 합니다.  
* **FFI Sync**: Rust의 구조체(Struct)가 변경되면, tools/codegen이 작동하여 Deno FFI 바인딩 정의와 TS 인터페이스를 즉시 동기화합니다.

---

## **2\. 규범: 언어별 코드 품질 및 스타일 가드**

### **\[2.1\] TypeScript / Deno (The Governance Layer)**

* **Linter**: Deno 내장 린터를 사용하되, **Trinity 패턴(Hexagonal+Functional+CQS)** 준수 여부를 검사하는 커스텀 규칙을 적용합니다.  
* **Explicit Context Injection**: 모든 비동기 함수 인자에 ctx: KrepisContext가 포함되어 있는지 정적 분석 단계에서 검사합니다.  
* **No Unsafe Deno**: 비즈니스 로직(packages/\*)에서 직접적인 Deno.unsafe 또는 네이티브 FFI 호출을 금지합니다. 모든 네이티브 접근은 packages/core의 브릿지를 통해서만 수행되어야 합니다.

### **\[2.2\] Rust (The Performance Layer)**

* **Strict Clippy**: \#\!\[deny(clippy::all, clippy::pedantic)\]를 강제하여 극한의 성능과 안전성을 확보합니다.  
* **Zero-Copy Principle**: TS로 데이터를 넘길 때 불필요한 메모리 복사가 발생하는 로직은 코드 리뷰 단계에서 반려됩니다.  
* **Explicit Panic Handling**: 커널 내부에서 panic\! 사용을 지양하고, 모든 에러는 Result 타입을 통해 TS 레이어의 KrepisNativeException으로 전파되도록 설계합니다.

---

## **3\. 검증: 아키텍처 가드 및 테스트 자동화**

### **\[3.1\] 결정적 아키텍처 가드 (AST Guard)**

* **Dependency Cruiser**: Deno 환경에 최적화된 종속성 그래프 분석을 통해 계층 침범을 감시합니다.  
* **Layer Isolation**: Domain 레이어는 Infrastructure 또는 Deno 전역 객체에 의존할 수 없습니다. 오직 순수 함수와 인터페이스로만 구성되어야 합니다.

### **\[3.2\] 통합 시뮬레이션 테스트 전략**

* **Standard Test**: TS Mock Kernel을 사용하여 비즈니스 로직의 논리적 완결성을 테스트합니다.  
* **Turbo Test**: 실제 Rust 커널과 FFI로 연결된 상태에서 성능 지표와 메모리 누수 여부를 테스트합니다.  
* **Shadow Validation**: 실제 운영 트래픽 로그를 기반으로 AI가 생성한 코드가 기존 로직과 동일한 결과를 내는지 대조 검증합니다.

---

## **4\. 소통: 협업 및 커밋 표준**

### **\[4.1\] Sovereign Commit Standard**

* **Scope 강제**: feat(kernel):, fix(ffi):, refactor(domain): 등 시스템 레이어를 명확히 구분합니다.  
* **Pre-commit Hook**: Deno의 내장 fmt 및 lint를 통과하지 못한 커밋은 로컬에서 원천 차단됩니다.

### **\[4.2\] 단일 진실 공급원 (Single Source of Truth)**

* **FFI Schema-Driven**: Rust와 TS 간의 모든 인터페이스는 crates/ffi-definition에서 관리됩니다.  
* **Manual Bridge Forbidden**: 수동으로 FFI 호출 코드를 작성하는 것을 금지하며, 반드시 자동 생성된 바인딩 코드를 사용해야 합니다.

---

## **4\. 핵심 가치 요약 (The Quality Pillars v1.5.0)**

| 가치 | 설명 | 기술적 실현 |
| :---- | :---- | :---- |
| **Unified Tooling** | 도구 파편화 제거 | Deno 내장 도구 \+ Cargo 워크스페이스 |
| **FFI Integrity** | 네이티브-런타임 무결성 | 자동화된 FFI 바인딩 및 타입 생성 |
| **Trinity Enforcement** | 아키텍처 규칙 강제 | AST 기반 린트 및 계층 침범 감시 |
| **Dual-Test Bed** | 이원화 엔진 통합 검증 | Standard/Turbo 통합 테스트 파이프라인 |

---