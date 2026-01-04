# 🛡️ Krepis Sovereign SDK

**Version**: 0.1.0 (Task 1 완료)  
**Architecture**: Trinity (Context → Pipeline → Behavior)  
**Runtime**: Deno 1.x+  
**License**: Proprietary

---

## 📖 개요

Krepis SDK는 **Rust 기반 Sovereign Kernel**과 **TypeScript 비즈니스 로직**을 연결하는 AI-Native 개발 플랫폼의 핵심 인터페이스입니다.

### 핵심 설계 원칙

1. **Explicit Context Propagation**: 모든 연산이 명시적 컨텍스트를 전달받음 (No AsyncLocalStorage)
2. **Zero-copy FFI**: Rust와 TS 간 데이터 전달 시 포인터만 교환 (성능 최적화)
3. **RAII Memory Safety**: Explicit Resource Management로 메모리 누수 방지
4. **Deterministic Error Handling**: 모든 에러가 구조화되고 재현 가능

---

## 🏗️ 아키텍처 (Trinity Model)

```
┌─────────────────────────────────────────────────────┐
│                   KrepisClient                      │  ← High-Level API
│                  (Task 3+)                          │
├─────────────────────────────────────────────────────┤
│              Pipeline & Middleware                  │  ← Execution Flow
│                  (Task 2)                           │
├─────────────────────────────────────────────────────┤
│           Behaviors (Bridge, Telemetry)             │  ← Concrete Logic
│                  (Task 2)                           │
├─────────────────────────────────────────────────────┤
│       Platform FFI Layer (COMPLETED ✅)             │  ← Raw Bridge
│    - layout.ts: Memory Layout                      │
│    - loader.ts: Dynamic Library Loader             │
│    - envelope.ts: Protobuf Unwrapper               │
├─────────────────────────────────────────────────────┤
│           Rust Sovereign Kernel                     │  ← Native Core
│    - SovereignPool (Multi-tenant Isolates)         │
│    - V8 Integration (JavaScript Execution)         │
│    - Resource Quotas (Tier-based Limits)           │
└─────────────────────────────────────────────────────┘
```

---

## 🚀 빠른 시작

### 1. 사전 요구사항

- **Deno**: 1.37 이상
- **Rust**: 1.70 이상 (커널 빌드용)
- **OS**: Linux (x86_64, aarch64), macOS (x86_64, Apple Silicon), Windows (x86_64)

### 2. 커널 빌드

```bash
# Krepis 커널 빌드
cd crates/krepis-kernel
cargo build --release

# SDK bin 디렉토리로 복사 (macOS Apple Silicon 예시)
mkdir -p ../../packages/krepis-sdk/bin/darwin-aarch64
cp target/release/libkrepis_kernel.dylib ../../packages/krepis-sdk/bin/darwin-aarch64/
```

### 3. SDK 사용

```typescript
import { loadKernelFFI, unwrapFfiResponse } from "@krepis/sdk";

// 커널 로드
const kernel = loadKernelFFI();

// Context 생성
const encoder = new TextEncoder();
const requestId = "my-request-001";
const requestIdBytes = encoder.encode(requestId);

const bufferPtr = kernel.symbols.create_context(
  requestIdBytes,
  requestIdBytes.length,
  false // is_turbo_mode
);

// FfiResponse Unwrap
try {
  const payload = unwrapFfiResponse(bufferPtr, kernel.symbols.free_buffer);
  console.log("✅ Context created:", payload);
} catch (err) {
  if (err instanceof KrepisBridgeError) {
    console.error("❌ Kernel error:", err.toJSON());
  }
}
```

---

## 📂 디렉토리 구조

```
packages/krepis-sdk/
├── src/
│   ├── platform/          # [Platform Layer]
│   │   └── ffi/           # Raw FFI Bridge (Task 1 ✅)
│   │       ├── layout.ts
│   │       ├── loader.ts
│   │       ├── envelope.ts
│   │       ├── mod.ts
│   │       └── ffi_bridge_test.ts
│   ├── core/              # [Core Layer] (Task 2)
│   │   ├── context/       # KrepisContext, Lifecycle
│   │   ├── pipeline/      # Middleware Engine
│   │   └── di/            # Dependency Injection
│   ├── behaviors/         # [Behavior Layer] (Task 2)
│   │   ├── bridge/        # FFI Call Behaviors
│   │   └── telemetry/     # CPI Measurement
│   └── client.ts          # [Client Layer] (Task 3+)
├── bin/                   # Platform-specific binaries
│   ├── linux-x86_64/
│   ├── darwin-aarch64/
│   └── windows-x86_64/
├── mod.ts                 # Public API Entry Point
├── deno.json              # Deno Configuration
├── TASK_001_REPORT.md     # Task 1 완료 보고서
└── README.md              # This file
```

---

## 🧪 테스트

```bash
# 모든 테스트 실행
deno task test

# FFI 레이어만 테스트
deno task test:ffi

# Linting & Formatting
deno task lint
deno task fmt

# Type Checking
deno task check
```

---

## 📊 현재 진행 상황

| Task | 구성요소 | 상태 | 비고 |
|------|---------|------|------|
| **Task 1** | **Raw FFI Bridge** | **✅ 완료** | layout, loader, envelope |
| Task 2 | Context & Pipeline | 🔄 대기 | IKrepisContext 구현 필요 |
| Task 3 | Behaviors | 🔄 대기 | Bridge, Telemetry |
| Task 4 | Client API | 🔄 대기 | KrepisClient |
| Task 5 | Integration Tests | 🔄 대기 | E2E 시나리오 |

---

## 🔧 개발 가이드라인

### Trinity 원칙

1. **Context**: 모든 함수가 `ctx: IKrepisContext`를 명시적으로 받음
2. **Pipeline**: 비즈니스 로직을 Middleware 체인으로 구성
3. **Behavior**: 원자적 작업 단위로 분리 (SRP 준수)

### 코딩 규칙

- ✅ **Explicit over Implicit**: 암시적 상태 전파 금지
- ✅ **Memory Safety**: RAII 패턴 사용 (using 구문)
- ✅ **Type Safety**: strict 모드, noImplicitAny 활성화
- ✅ **Error Handling**: 모든 에러가 KrepisBridgeError로 통합

### Commit Convention

```
feat(ffi): Add envelope unwrapper with Protobuf support
fix(loader): Handle missing binary gracefully
refactor(layout): Extract type guards to separate file
test(ffi): Add integration test for create_context
```

---

## 🎯 다음 단계 (Roadmap)

### Task 2: Context & Pipeline

- [ ] `src/core/context/KrepisContext.ts` - Protobuf 래퍼 구현
- [ ] `src/core/pipeline/Pipeline.ts` - Middleware 엔진
- [ ] `src/core/di/Container.ts` - DI 컨테이너

### Task 3: Behaviors

- [ ] `src/behaviors/bridge/CreateContextBehavior.ts`
- [ ] `src/behaviors/bridge/InitializeKernelBehavior.ts`
- [ ] `src/behaviors/telemetry/CpiMeasurementBehavior.ts`

### Task 4: Client API

- [ ] `src/client.ts` - KrepisClient 클래스
- [ ] SDK 사용 예제 및 튜토리얼

---

## 📖 참조 문서

- **아키텍처 스펙**
  - [Spec-Dev-001] Memory Safety v1.6.0
  - [Spec-Dev-002] Sovereign Bridge v1.1.0
  - [Spec-002] DI Module v1.2.0
  - [Spec-Sovereign-003] Resource Quota v1.0.0

- **커널 소스**
  - `crates/krepis-kernel/src/ffi/bridge.rs`
  - `proto/error.proto`, `proto/context.proto`

- **개발 가이드**
  - [TASK_001_REPORT.md](./TASK_001_REPORT.md)

---

## 🤝 기여 가이드

Krepis는 AI Chief Architect (K-ACA)와의 협업을 통해 개발됩니다.

### 개발 프로세스

1. **Spec 확인**: 항상 최신 Sovereign Spec 준수
2. **Micro Tasking**: 모든 작업을 Super Micro Task로 분할
3. **Test-Driven**: 테스트 코드 먼저 작성
4. **Review**: K-ACA의 아키텍처 검토 통과 필수

---

## 📜 라이선스

Proprietary - Krepis Project  
© 2026 Krepis Development Team

---

**🏁 Current Status: Task 1 COMPLETE**

> "당신은 이제 Krepis의 수석 아키텍트이자 AI 군단 총사령관입니다."  
> — K-ACA v2.0

진혁님의 검토를 기다립니다. 🙏