# 📄 krepis_spec_sovereign_002.md

**Title:** Tenant Context Identification & Resource Mapping Specification

**Version:** 1.0.0

**Status:** Draft

**Scope:** Multi-tenant Identity Verification and Resource Virtualization

---

## 1. Identity Extraction & Verification

시스템 진입점(Ingress)에서 테넌트의 신원을 보증한다.

* **Identity Source**: 표준 HTTP/gRPC 헤더인 `X-Krepis-Tenant-ID` 또는 `Authorization` Bearer 토큰의 `sub` 클레임을 기본 식별자로 사용한다.
* **Immediate Validation**: `SovereignPool`에서 Isolate를 점유하기 전, 커널의 **Identity Cache (LRU)**를 조회하여 테넌트의 활성 상태와 구독 등급을 즉시 검증한다. 캐시에 없는 경우에만 외부 Auth 제공자에 질의하여 지연 시간을 최소화한다.

## 2. Storage & Namespace Virtualization (Pingora-style)

물리적 오버헤드를 줄이기 위해 단일 DB 내에서 논리적 격리를 수행한다.

* **Logical Partitioning**: Sled DB의 `open_tree` API를 사용하여 각 테넌트에게 전용 Tree를 할당한다.
* *Naming Convention*: `tenant_db_{tenant_id}`


* **Zero-Knowledge Storage**: 테넌트 JS 코드는 직접적인 Tree 이름을 알 필요가 없으며, 오직 `op_storage_set/get` 등의 추상화된 API를 통해 자신에게 할당된 공간에만 접근한다.

## 3. Runtime Context Propagation

Rust 호스트에서 결정된 메타데이터를 JS 실행 환경에 안전하게 주입한다.

* **Pre-Injected Context (Push)**: Isolate 생성 시 `Deno.core.ops.op_get_context()`를 통해 스냅샷 형태로 데이터를 전달하되, 자주 사용되는 정보(TenantID, RequestID)는 `globalThis.Krepis` 네임스페이스에 읽기 전용으로 미리 주입(Freeze)하여 JS 단의 호출 오버헤드를 줄인다.

## 4. Virtualized Path Mapping (Chroot-like)

테넌트 코드가 시스템 파일에 직접 접근하는 것을 원천 차단한다.

* **Path Remapping**: JS에서 `/app/data/config.json`과 같은 경로로 입출력을 시도할 경우, Rust 커널 레이어에서 이를 `root/tenants/{tenant_id}/data/config.json`으로 자동 리매핑한다.
* **Isolation Integrity**: 테넌트 코드는 자신이 시스템의 어느 물리적 경로에 있는지 알 수 없으며, 할당된 가상 루트 디렉터리 상위로 이동(Path Traversal)할 수 없다.

## 5. Metadata & Secrets Protocol

확장성과 보안을 위한 표준 메타데이터 규약을 정의한다.

* **Krepis Metadata Standards**:
* `ENV_*`: 테넌트 전용 환경 변수.
* `SEC_*`: 암호화되어 저장된 비밀 정보(API Key 등). Rust 레이어에서 복호화되어 JS에는 결과값만 전달된다.


* **Immutable Metadata**: 실행 중에는 컨텍스트 내의 메타데이터를 JS에서 수정할 수 없으며, 모든 상태 변경은 `journal`을 통해서만 기록된다.

---