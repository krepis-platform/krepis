# 📄 [Spec-Dev-002] Sovereign Bridge Specification v1.1.0

**Project**: Krepis Sovereign Platform

**Category**: Development Infrastructure / Native Bridge

**Last Updated**: 2026. 01. 03

**Author**: Krepis Lead Architect

---

## 1. 서론 (Introduction)

본 명세서는 Krepis Sovereign Kernel(Rust)과 SDK(TypeScript/Deno) 간의 저수준 인터페이스인 **'Sovereign Bridge'**를 정의한다. 이 브릿지는 '초결정성(Determinism)'과 'Zero-copy' 성능을 목표로 하며, 메모리 안전성과 강한 격리 원칙을 준수한다.

## 2. 물리적 계층 규격 (Physical Layer Specification)

### 2.1 ABI Stability & FfiBuffer Layout

Rust와 TS 간의 데이터 교환을 위한 핵심 구조체인 `FfiBuffer`는 64비트 시스템에서의 데이터 무결성을 위해 8바이트 정렬(Alignment)을 강제한다.

```rust
#[repr(C, align(8))]
pub struct FfiBuffer {
    pub data: *mut u8,      // 0-7: 데이터 포인터 (Raw Pointer)
    pub len: usize,         // 8-15: 실제 유효 데이터 길이
    pub cap: usize,         // 16-23: 할당된 메모리 총 용량
    pub _padding: u64,      // 24-31: ABI 안정성을 위한 명시적 패딩
}

```

### 2.2 Handshake & Versioning

초기화 단계에서 SDK와 커널 간의 바이너리 호환성을 검증한다.

* **Handshake Protocol**: SDK는 `initialize_kernel` 호출 시 `uint32` 버전 코드를 전달한다.
* **Compatibility Check**: 커널은 내부 `ABI_HASH`와 대조하여 불일치 시 실행을 거부하고 전용 에러 코드를 반환한다.

## 3. 프로토콜 레이어 (Protocol Layer)

### 3.1 FfiResponse Envelope System

모든 커널 호출의 응답은 `FfiResponse` Protobuf 메시지로 캡슐화된다. 이는 성공 데이터와 에러 메타데이터를 통합 관리하는 단일 창구 역할을 한다.

### 3.2 Error Propagation & Diagnostics

에러 발생 시 단순 메시지가 아닌 실행 환경의 스냅샷을 포함한다.

* **KrepisError**: 에러 코드, 스택 트레이스, 테넌트 정보 및 `ResourceSnapshot` 포함.
* **ResourceSnapshot**: 타임아웃 발생 시점의 `heap_used_bytes`, `elapsed_ms`, `limit_ms` 정보를 담아 AI의 자율 치유(Self-healing) 근거 데이터로 활용.

## 4. 메모리 관리 정책 (Memory Management)

### 4.1 Ownership & Lifecycle

* **Rust-to-TS**: 커널이 반환한 `*mut FfiBuffer`의 소유권은 일시적으로 SDK에 이전된다. SDK는 데이터 사용 후 반드시 `free_buffer` FFI를 호출하여 커널에 소유권을 반환해야 한다.
* **TS-to-Rust**: SDK가 생성한 데이터(Input)는 Rust 레이어에서 디코딩 완료 즉시 TS 메모리에서 해제되도록 설계한다.

### 4.2 Explicit Resource Management (ERM)

SDK는 `Symbol.dispose`를 사용하여 메모리 해제를 자동화한다. 블록을 벗어나는 즉시 `free_buffer`가 호출되도록 강제한다.

## 5. 실행 제어 및 격리 (Execution & Isolation)

### 5.1 Explicit Context Injection

`AsyncLocalStorage`와 같은 암시적 상태를 배제한다. 모든 FFI 호출은 첫 번째 인자로 `KrepisContext` 바이너리를 전달받아야 한다.

* **Context Content**: `request_id`, `tenant_id`, `trace_id`, `is_turbo_mode` 등.
* **Audit Trail**: 모든 컨텍스트 정보는 `SovereignJournal`과 연동되어 실행 이력을 추적한다.

### 5.2 Preemptive Watchdog & Failover

물리적 감시 스레드가 실행을 중단시킨 경우, 브릿지는 즉시 응답을 가로채어 `ERROR_CODE_EXECUTION_TIMEOUT`을 전파한다.

* **Zero-Inertia Switching**: 커널 패닉 감지 시 SDK는 즉시 Standby 인스턴스로 트래픽을 스위칭하는 안전장치를 가동한다.

## 6. 호출 경로 최적화 (Path Optimization)

| 경로명 | 호출 방식 | 대상 작업 | 최적화 기술 |
| --- | --- | --- | --- |
| **Fast Path** | Synchronous | 메타데이터 조회, 로그 기록, 컨텍스트 획득 | Deno FFI Fast Call, Direct Memory Access |
| **Standard Path** | Asynchronous | 스크립트 실행, 저널 커밋, 대규모 데이터 처리 | Rust Tokio Worker, Promise Bridge |

## 7. 부록: FFI Export 인터페이스 (C-ABI)

```c
// 핵심 커널 익스포트 함수 명세
FfiBuffer* initialize_kernel(const uint8_t* buffer_ptr, size_t buffer_len);
FfiBuffer* create_context(const uint8_t* id_ptr, size_t id_len, bool is_turbo);
FfiBuffer* execute_isolated(const uint8_t* ctx_ptr, size_t ctx_len, const char* script);
void free_buffer(FfiBuffer* ptr);

```

---