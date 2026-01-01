# **📑 \[Krepis\] 0\. 개요: 하이브리드 모노레포 전략 상세 명세 (v1.5.0)**

버전: v1.5.0 (The Sovereign Hybrid)

분류: 시스템 아키텍처 및 워크스페이스 구조

## **0.1 아키텍처 비전 (Sovereign Core Architecture)**

Krepis는 성능 지향적 시스템 프로그래밍(**Rust**)과 결정적 런타임 위에서의 유연한 비즈니스 오케스트레이션(**Deno/TypeScript**)을 결합합니다. 모든 제어권은 Rust 기반의 Sovereign Kernel이 쥐며, 비즈니스 로직은 명시적 컨텍스트(Explicit Context)를 통해 안전하게 실행되는 **'통제된 하이브리드'** 구조를 지향합니다.

## **0.2 핵심 전략 명세**

### **1\. 역할 분담 및 확장성 (Sovereign Layering)**

* **Sovereign Kernel (Rust):** KNUL 프로토콜 패킷 전송, **Hyper-Pingora** 기반 서버 엔진, 프로세스 격리(Sandbox), 그리고 Deno 런타임을 임베딩하거나 제어하는 마스터 역할을 수행합니다.  
* **Business Logic (Deno/TS):** Trinity 패턴(Hexagonal+Functional+CQS) 기반의 실제 아키텍처 명세와 도메인 로직을 담당합니다.  
* **Native Bridge:** 모든 네이티브 기능은 \*\*Deno FFI(Foreign Function Interface)\*\*를 통해 TypeScript에 인터페이스 형태로 노출됩니다. 기존의 NAPI-RS 의존성을 제거하여 런타임 오버헤드를 최소화합니다.

### **2\. 배포 및 설치 전략 (Native Artifact Delivery)**

* **표준 방식:** 운영체제별 사전 빌드된 **Sovereign Core Binary (.so, .dll, .dylib)** 배포를 채택합니다.  
* **메커니즘:** CI(GitHub Actions)에서 x86\_64, arm64 등 타겟별 바이너리를 빌드합니다. Deno의 모듈 관리 시스템을 통해 필요한 바이너리를 런타임에 자동으로 fetch하거나 설치 시점에 포함합니다.  
* **이점:** 사용자는 Rust 툴체인이나 복잡한 빌드 도구 없이 Deno 실행 환경만으로 즉시 Krepis의 네이티브 가속을 누릴 수 있습니다.

### **3\. 데이터 교환 및 직렬화 (Zero-copy Sovereignty)**

* **표준 방식:** **Zero-copy Shared Memory** 및 **Protobuf**를 사용합니다.  
* **상세:** \* **Control Plane:** 가벼운 제어 신호는 Protobuf로 규격화하여 Rust-TS 간 정합성을 보장합니다.  
  * **Data Plane:** 대규모 AST나 패킷 데이터는 **Deno.UnsafePointer**를 사용하여 Rust가 할당한 메모리를 TS 레이어에서 복사 없이 직접 참조(Read-only)함으로써 I/O 병목을 근본적으로 차단합니다.

### **4\. 개발 환경 통합 (Deno-Cargo Orchestration)**

* **표준 방식:** **Deno Tasks**와 **Cargo Workspaces**를 연동한 단일 파이프라인을 구축합니다.  
* **DX 최적화:** deno task dev 실행 시, Rust 커널은 cargo watch를 통해 변경을 감지하고, TS 로직은 Deno의 기본 핫 리로딩 기능을 활용하여 즉각적인 피드백 루프를 형성합니다.  
* **캐싱:** Heavy한 Rust 빌드는 Cargo의 증분 빌드(Incremental Build)와 sccache를 활용하여 가속합니다.

### **5\. 버전 관리 정책 (Sovereign Lock-step)**

* **표준 방식:** \*\*Single-version Policy (Lock-step)\*\*를 채택합니다.  
* **이유:** Rust 커널과 TS FFI 바인딩 간의 ABI(Application Binary Interface) 호환성을 보장하기 위해 모든 컴포넌트는 동일한 버전 번호를 공유합니다. 이는 cargo-release 및 커스텀 스크립트를 통해 관리됩니다.

### **6\. 런타임 보안 및 샌드박스 (Sovereign Guard)**

* **표준 방식:** **Deno Permission Model \+ Rust Kernel Guard.**  
* **상세:** Deno의 강력한 권한 제어(\--allow-net, \--allow-read 등)를 기본으로 사용하되, 고수준 보안이 필요한 작업은 Rust 커널 레이어에서 직접 시스템 콜을 감시하거나 격리된 프로세스 환경(Sandbox)에서 수행하도록 강제합니다.

## **0.3 하이브리드 워크스페이스 구조 (v1.5.0)**

Plaintext

/ (Root)  
├── Cargo.toml            \# Rust Workspace (kernel, cli, native\_addons)  
├── deno.json             \# Deno Task, Import Map, Lint/Fmt Config  
├── .krepis/              \# Local Sled DB & Transaction Logs  
├── crates/  
│   ├── krepis-kernel/    \# Hyper-Pingora 기반 Sovereign Kernel (Rust)  
│   ├── krepis-cli/       \# Rust Native Master CLI  
│   └── krepis-ffi/       \# TS 바인딩 자동 생성을 위한 FFI 정의  
├── packages/  
│   ├── core/             \# Deno-based Trinity Framework Core (TS)  
│   ├── smart-gen/        \# AST Manipulation Engine (TS)  
│   └── shared/           \# Common TS Types & Utils  
└── tools/  
    └── codegen/          \# Rust-to-TS FFI Binding Generator

---
