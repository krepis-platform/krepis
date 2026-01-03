# **📑 [Spec-Dev-001] 통합 빌드 및 메모리 안전 규격 (v1.6.0)**

**버전:** v1.6.0 (Memory Safety & Zero-copy Concurrency)
**상태:** 최종 확정 (Finalized)
**핵심 보완 사항:** GC 독립적 포인터 유지 방식, Shared Memory Lock 메커니즘 명문화

---

## **1. FFI 브릿지의 메모리 안전성 (Memory Safety)**

### **1.1 GC-Independent Pointer Preservation**

Rust 커널이 생성한 메모리가 TS의 가비지 컬렉션 타이밍에 의해 예기치 않게 해제되거나 이동되는 것을 방지하기 위해 다음 전략을 사용합니다.

* **Manual Ownership Management (Rust Side):** - 커널은 `Vec<u8>` 또는 구조체를 생성한 후 `std::mem::forget`을 호출하거나 `Box::into_raw`를 통해 Rust의 자동 해제 메커니즘(RAII)을 일시 정지시킵니다.
* 이로 인해 해당 메모리는 물리 주소에 고정(Pinned)되며, TS 레이어에서 명시적인 해제 신호(`free_buffer`)를 보내기 전까지 GC의 영향권 밖에서 안전하게 유지됩니다.


* **External Reference (TS Side):** - Deno FFI를 통해 전달된 포인터는 `Deno.UnsafePointerView`를 통해 `ArrayBuffer`로 래핑됩니다.
* 이때 해당 Buffer는 TS의 힙(Heap) 메모리가 아닌 **External 메모리**로 분류되어 GC가 주소를 옮기거나 임의로 회수하지 못하도록 보호됩니다.



### **1.2 Shared Memory Race Condition 방지 대책**

`SharedArrayBuffer`를 통해 두 레이어가 동일 메모리 영역을 참조할 때, 데이터 일관성을 보장하기 위해 **'상태 기반 소유권 락(State-based Ownership Lock)'**을 도입합니다.

* **Atomic State Flag (Header 영역):** - `FfiBuffer`의 시작 부분에 4바이트의 `AtomicU32` 상태 플래그를 배치합니다.
* `0: KERNEL_OWNED` (Rust 쓰기 중), `1: SDK_OWNED` (TS 읽기/쓰기 중), `2: LOCKED` (동기화 중).


* **Locking Mechanism:**
* **Rust -> TS:** 커널이 쓰기를 완료하면 상태를 `1`로 변경합니다. TS는 이 상태가 `1`이 될 때까지 Non-blocking wait(혹은 Atomics.wait)를 수행합니다.
* **TS -> Rust:** TS가 처리를 마치고 `free_buffer`를 호출하면, 상태를 다시 `0`으로 되돌려 커널이 재사용할 수 있게 합니다.


* **ReadOnly Protection:** 공유 메모리 영역이 "읽기 전용"으로 선언된 경우, 커널 레이어에서 `mprotect`를 통해 물리적 쓰기 금지를 강제하여 교묘한 로직 오염을 차단합니다.

---

## **2. 아티팩트 및 바인딩 관리 고도화**

### **2.1 Bindings Codegen: Safety-First**

`tools/codegen`은 단순히 함수 이름만 추출하는 것이 아니라, 메모리 소유권 규칙을 코드 레벨에서 생성합니다.

* **Automatic Disposer:** TS의 `using` 키워드와 결합할 수 있도록 `[Symbol.dispose]`가 구현된 클래스를 자동 생성합니다.
* **Type Alignment Check:** Rust의 `Layout::array::<T>`와 TS의 `TypedArray` 오프셋이 일치하는지 검수하는 정적 체크섬 코드를 바인딩에 포함합니다.

---

## **3. 런타임 브릿지 워크플로우 (Atomic Interaction)**

1. **Allocation:** 커널이 요청을 받으면 `FfiBuffer`를 할당하고 포인터를 고정합니다.
2. **State Init:** 상태 플래그를 `0(Kernel)`으로 설정하고 데이터를 기록합니다.
3. **Handoff:** 상태를 `1(SDK)`로 원자적 변경(Atomic CAS) 후 포인터를 반환합니다.
4. **Access:** SDK는 상태가 `1`임을 확인하고 데이터를 소비합니다.
5. **Reclaim:** `using` 블록 종료 시 `free_buffer`가 호출되어 커널이 메모리를 회수하거나 풀(Pool)로 반환합니다.

---

## **4. 빌드 설정 및 성능 최격화 (Update)**

* **SIMD 가속:** Shared Memory 처리 시 CPU의 SIMD 명령어를 활용하여 체크섬 검증 및 데이터 복사를 가속화합니다.
* **Zero-Copy 패스:** 대용량 데이터(1MB 이상)의 경우 복사 없이 포인터만 교환하며, 소용량 데이터는 FFI 오버헤드 방지를 위해 인라인 직렬화를 선택적으로 사용합니다.

---