# **📑 [Krepis-Spec-000] 시스템 아키텍처 및 하이브리드 전략 통합 명세서 (v1.6.0)**

**버전:** v1.6.0 (The Unified Sovereign Architecture)
**분류:** 시스템 아키텍처, 물리적 구조 및 핵심 기술 스택
**상태:** 최종 병합본 (Merged)

---

## **1. 아키텍처 비전 (Sovereign Core Architecture)**

Krepis는 성능 지향적 시스템 프로그래밍(**Rust**)과 결정적 런타임 위에서의 유연한 비즈니스 오케스트레이션(**Deno/TypeScript**)을 결합한 **'통제된 하이브리드(Sovereign Hybrid)'** 아키텍처를 지향합니다.

* **Sovereign Control:** 모든 시스템 제어권(메모리, 네트워킹, 스레딩)은 Rust 기반의 Sovereign Kernel이 쥡니다.
* **Explicit Execution:** 비즈니스 로직은 명시적 컨텍스트(Explicit Context)를 통해 안전하고 예측 가능한 방식으로 Deno 런타임 위에서 실행됩니다.
* **No Compromise:** 개발 편의성(TS)과 실행 성능(Rust) 사이의 타협 없이, **Deno FFI**를 통해 두 세계를 Zero-copy로 연결합니다.

---

## **2. 하이브리드 워크스페이스 구조 (Physical Layout)**

Krepis는 **Cargo Workspaces**(Rust)와 **Deno Workspaces**(TS)가 공존하는 단일 모노레포 구조를 채택합니다.

```plaintext
/ (Root)
├── Cargo.toml            # Rust Workspace Root (Workspace Member 정의)
├── deno.json             # Deno Workspace Root (Import Map, Tasks, Lint)
├── .krepis/              # Local Runtime Data (Sled DB & Transaction Logs)
├── crates/               # [The Engine Room] - Rust Native Code
│   ├── krepis-kernel/    # Hyper-Pingora 기반 Sovereign Kernel & KNUL 엔진
│   ├── krepis-cli/       # Rust Native Master CLI & Orchestrator
│   └── krepis-ffi/       # TS 바인딩 자동 생성을 위한 FFI Definition
├── packages/             # [The Business Floor] - TypeScript Code
│   ├── core/             # Trinity 패턴 기반 프레임워크 코어 (SDK)
│   ├── smart-gen/        # ts-morph 기반 AST 조작 엔진
│   └── cli/              # 아키텍처 검수 도구 및 CLI 플러그인
└── tools/                # [The Factory] - Build & Codegen Tools
    └── codegen/          # Rust-to-TS FFI Binding Generator

```

---

## **3. 핵심 기술 전략 (Core Technology Strategy)**

### **3.1 Sovereign Layering (역할 분담)**

* **Sovereign Kernel (Rust):**
* **Role:** 하드웨어 리소스의 직접 통제, KNUL 프로토콜 처리, 샌드박스 격리.
* **Tech:** Hyper, Pingora, Tokio, Quinn.


* **Business Logic (Deno/TS):**
* **Role:** 실제 애플리케이션 아키텍처 정의, 도메인 로직 수행.
* **Tech:** Deno Runtime, Trinity Pattern (Hexagonal/CQS).


* **Native Bridge:**
* **Role:** 두 계층 간의 초고속 통신. 기존 NAPI-RS 대신 **Deno FFI**를 사용하여 오버헤드를 제거합니다.



### **3.2 Zero-copy Data Exchange (통신)**

* **Control Plane (Protobuf):** 가벼운 제어 신호 및 메타데이터는 Protobuf(`prost`)로 직렬화하여 타입 안전성을 보장합니다.
* **Data Plane (Shared Memory):** 대용량 패킷이나 AST 데이터는 **Deno.UnsafePointer**와 **SharedArrayBuffer**를 사용하여, Rust가 할당한 메모리를 TS가 복사 없이 직접 참조(Read-only)합니다.

### **3.3 CLI Orchestration & Isolation**

* **Master CLI (Rust):** 단순한 실행기가 아니라, Deno 하위 프로세스를 관리하는 **감독관(Supervisor)**입니다.
* **V8 Isolate Sandbox:** 각 플러그인이나 태스크 실행 시 독립된 V8 Isolate를 생성하여, 하나의 오류가 커널 전체를 무너뜨리지 않도록 물리적으로 격리합니다.
* **Transactional FS (Sled):** 파일 조작 전 스냅샷을 `sled` DB에 기록하여, `krepis undo` 명령 시 즉각적인 롤백을 보장합니다.

---

## **4. 배포 및 개발 워크플로우 (Delivery & DX)**

### **4.1 Native Artifact Delivery**

* **Pre-built Binaries:** 사용자는 Rust 툴체인을 설치할 필요가 없습니다. OS별(Windows, macOS, Linux)로 최적화된 `.so`, `.dll`, `.dylib` 바이너리가 CI에서 빌드되어 배포됩니다.
* **Dynamic Loading:** `krepis init` 시 Deno가 런타임에 맞는 바이너리를 자동으로 다운로드하고 캐싱합니다.

### **4.2 Unified Dev Pipeline**

* **Hot-Reload Sync:** `deno task dev` 실행 시, Rust 커널은 `cargo watch`로, TS 로직은 Deno의 핫 리로딩으로 각각 변경을 감지하며, 변경 사항은 즉시 동기화됩니다.
* **Smart Generator:** `ts-morph` 기반의 생성기가 코드 작성 시 **`ctx: KrepisContext`** 인자 누락을 실시간으로 감지하고 빌드를 차단합니다.

### **4.3 Sovereign Governance**

* **Plugin Validation:** 서드파티 플러그인은 마켓플레이스 등록 전 Deno Permission Model 기반의 정적 분석과 AI Sentinel의 검수를 통과해야 합니다.
* **Digital Signature:** 검증된 플러그인에는 네이티브 서명이 부여되며, 커널은 실행 시 이 서명을 강제 확인합니다.

---

## **5. 핵심 가치 요약 (The Infrastructure Pillars)**

| 가치 | 설명 | 기술적 실현 |
| --- | --- | --- |
| **Hybrid Sovereignty** | 성능(Rust)과 생산성(TS)의 완벽한 조화 | Sovereign Kernel + Deno FFI |
| **Zero-copy I/O** | 데이터 복사 없는 초고속 인터페이스 | Shared Memory Pointer & Protobuf |
| **Physical Isolation** | 장애 전파가 없는 견고한 실행 환경 | V8 Isolate Sandbox + Sled Rollback |
| **Single Repo** | 모든 코드를 한곳에서 관리하는 효율성 | Cargo & Deno Workspace 통합 |

---