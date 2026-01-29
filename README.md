# Krepis: Sovereign AI-Native ADaaS Platform

> **Architecture Development as a Service - v2.1.0 (The Deterministic Link)**

## 🎯 Core Philosophy

**Sovereign Control, Fractal Intelligence**

* **Systemic Rigidity**: Rust + Deno for deterministic runtime.
* **Fractal Intelligence**: Master-Expert-Atomic Executor legion architecture.
* **Explicit Context**: Zero implicit state propagation via `IKrepisContext`.
* **Sovereign Link (KNUL)**: Native QUIC stack with zero-copy SPSC handoff.

## 🏗️ Architecture Overview

### Hybrid Sovereign Monorepo

```
krepis/
├── Cargo.toml              # Rust workspace root
├── deno.json               # Deno runtime config
├── crates/
│   ├── krepis-twin/        # Digital Twin Simulation for All of Components
│   ├── krepis-kernel/      # Sovereign Kernel Host (Rust embeds Deno)
│   │   └── src/ops.rs      # Rust-JS bridge operations
│   ├── krepis-knul/        # 🆕 QUIC & SPSC Engine (Native Networking)
│   │   ├── src/server.rs   # Quinn v0.11 & PacketQueue
│   │   └── src/registry.rs # Thread-safe server management
│   └── krepis-core/        # ⚖️ Sovereign ABI (Source of Truth)
│       └── src/abi.rs      # FFI-safe layouts (ABI v1.1.0)
└── packages/
    ├── deno-krepis-knul/   # 🔗 KNUL Adapter (TypeScript)
    └── deno-krepis-core/   # 🧱 Core FFI Bindings (Symbol.dispose)

```

## ⚡ Technical Breakthrough: The Sovereign Link (KNUL)

v2.1.0에서는 네이티브 네트워크 패킷이 JavaScript 레이어까지 **단 1바이트의 복사도 없이(Zero-Copy)** 전달되는 물리적 통로를 완성했습니다.

### 1. Deterministic Packet Handoff

* **QUIC Engine**: `quinn` v0.11 기반의 고성능 전송 계층.
* **SPSC Queue**: Single Producer Single Consumer 패턴을 통한 지연 시간(Jitter) 제거.
* **Pointer Identity**: 네이티브에서 수신된 메모리 주소가 TS `UnsafePointerView`까지 동일하게 유지됨을 검증 완료.

### 2. ABI v1.1.0 (Sovereign Bridge)

* **Strict Alignment**: 64비트 시스템에서의 8바이트 정렬 강제.
* **Thread Safety**: `FfiBuffer`에 대한 `Send`/`Sync` 구현으로 멀티 스레드 환경에서의 안전한 포인터 공유.
* **Explicit Resource Management**: TypeScript `using` 구문과 `Symbol.dispose`를 통한 확정적 메모리 해제.

## 🚀 Quick Start

### Build & Test Native Engines

```bash
# Build workspace
cargo build --workspace

# Run Zero-copy Integrity Tests
cargo test -p krepis-knul --lib server::tests::test_packet_buffer_creation

```

### Run Deno Link Examples

```bash
cd packages/deno-krepis-knul
deno task examples

```

## 📐 Architecture Principles

### Control Plane vs Link Plane

```
┌────────────────────────────┐
│   Rust Control Plane       │  ← Sovereign Authority (Kernel)
└──────────┬─────────────────┘
           │ SPSC Queue (Zero-copy)
           ↓
┌────────────────────────────┐
│   KNUL Link Plane          │  ← High-speed Communication (QUIC)
└──────────┬─────────────────┘
           │ FFI Bridge
           ↓
┌────────────────────────────┐
│   Deno Execution Plane     │  ← Business Logic (AI Agents)
└────────────────────────────┘

```

## 📊 Performance & Safety Proof

* **Zero-Copy Proof**: `assert_eq!(packet.as_ptr(), original_ptr)` 테스트 통과.
* **Memory Safety**: ` catch_unwind`를 통한 FFI 경계에서의 패닉 전파 차단.
* **Concurrency**: `DashMap` 기반의 락-프리 서버 인스턴스 레지스트리 (10K+ 연결 대응).

## 🔐 Security Model

* **Rust-Managed TLS**: `rustls`를 통한 네이티브 레벨의 보안 종단점 관리.
* **Permissioned I/O**: Deno 레이어는 직접적인 소켓 접근 권한이 없으며, 오직 검증된 `FfiBuffer`만 수신 가능.
* **Context Integrity**: 모든 패킷은 `tenant_id`와 `trace_id`가 포함된 컨텍스트를 강제로 수반.

## 📝 License

Apache-2.0

---

**Status**: Phase 2.5 - KNUL Native Implementation Complete ✅ / Phase 3 - AI-Native Integration In-Progress 🚧

---