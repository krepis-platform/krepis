# **📑 \[Krepis Base Spec-002\] 차세대 통신 표준: KNUL 상세 명세서**

버전: v1.5.0 (The Deterministic Connectivity)

분류: 네트워크 프로토콜 및 데이터 전송 규격

## **1\. 프로토콜 레이어 및 연결 관리 (Connectivity)**

### **1.1 QUIC 기반 0-RTT 핸드셰이크 (Sovereign Level)**

* **구현 매커니즘:** Rust의 quinn 라이브러리를 **Hyper 네이티브 서버**와 통합하여 구현합니다.  
* **Session Resumption:** 첫 연결 시 서버로부터 발급받은 NewSessionTicket을 클라이언트 로컬의 고성능 KV 저장소인 **sled**에 저장합니다. 재연결 시 이 티켓을 활용해 0-RTT를 실현하며, 이 과정은 TS 레이어의 개입 없이 Rust 커널 내에서 즉각 처리됩니다.  
* **보안 정책:** 세션 티켓은 24시간 후 만료되며, IP 변경 시 보안을 위해 1-RTT로 강제 전환하여 세션 하이재킹을 방지합니다.

### **1.2 네트워크 적응성 및 Sovereign 가용성**

* **v1.x (Path Validation):** 표준 QUIC의 경로 검증 기능을 사용합니다.  
* **v2.x (Hole Punching):** 전용 STUN/TURN 로직을 KNUL 내부에 통합하여 NAT 환경에서도 P2P 효율을 확보합니다.  
* **Pingora Integration:** Pingora의 커넥션 풀링 로직을 활용하여 수만 개의 KNUL 스트림을 재사용하고 지연 시간을 최소화합니다.

---

## **2\. 하이브리드 데이터 처리 엔진 (Data Processing)**

### **2.1 분기형 직렬화 (Zero-copy Dispatch)**

데이터 성격에 따라 런타임이 통로를 결정합니다.

* **Protocol Buffers (Control Plane):** API 메시지, 제어 신호, 메타데이터에 사용합니다. Rust에서 파싱된 Protobuf 데이터는 Deno FFI를 통해 TS의 정적 타입 객체로 즉시 맵핑됩니다.  
* **TypedArray/SharedBuffer (Data Plane):** 1MB 이상의 대용량 바이너리 처리 시 사용합니다. \*\*Deno의 UnsafePointer와 TypedArray\*\*를 결합하여 Rust가 할당한 메모리 주소를 TS가 복사 없이 직접 참조(Zero-copy)하게 함으로써 I/O 병목을 제거합니다.

### **2.2 스키마 버전 관리 및 동적 바인딩**

* **Schema Registry:** BaaS 서버와 연동하여 최신 스키마를 체크하며, Deno 환경에서 필요 시 관련 TS 정의(Definition)를 동적으로 로드합니다.

---

## **3\. 고도화된 압축 및 가속 (Compression & Acceleration)**

### **3.1 하이브리드 시맨틱 사전 (Krepis-LZ)**

* **정적 사전 (Static):** 헥사고날/Trinity 패턴 상용 구문을 학습한 사전을 Rust 바이너리에 내장합니다.  
* **동적 사전 (Dynamic):** 프로젝트별 커스텀 도메인 용어를 런타임에 학습하여 세션 동안 압축률을 점진적으로 높입니다. 이 학습 과정은 비즈니스 로직에 영향을 주지 않도록 별도의 Rust 백그라운드 스레드에서 수행됩니다.

---

## **4\. 보안 및 신뢰성 (Security & Reliability)**

### **4.1 SIMD 가속 기반 패킷 서명 및 무결성**

* **SIMD 가속:** 모든 패킷 헤더의 서명 연산을 Rust의 SIMD 명령어로 병렬 처리하여 1ms 미만의 지연 시간을 보장합니다.  
* **Context Propagation:** traceId, tenantId, priority 정보를 QUIC 패킷 헤더에 배치합니다. **Rust 커널**은 페이로드를 복호화하기 전에 헤더만 읽고 해당 요청을 어느 TS Worker로 보낼지, 혹은 즉시 거절(Reject)할지 결정합니다.

---

## **5\. 브릿지 인터페이스 (Sovereign Bridge v1.5.0)**

### **5.1 Deno FFI 기반 Deterministic Bridge**

* **구현 방식:** 기존 Node.js의 Stream API(Node-specific) 대신, \*\*Deno FFI(Foreign Function Interface)\*\*를 통한 직접 호출 방식을 채택합니다.  
* **최적화 전략 (Event Loop Non-blocking):**  
  * Rust에서 수신된 대량 패킷은 Rust 측의 **SPSC(Single Producer Single Consumer) 큐**에 저장됩니다.  
  * TS 레이어는 Deno의 UnsafePointerView를 통해 큐에 접근하여 필요한 데이터만 가져옵니다.  
* **이유:** Event 기반의 비동기 전파보다 지연 시간이 짧고, **명시적 컨텍스트(Explicit Context)** 주입 시 데이터 유실을 물리적으로 차단할 수 있기 때문입니다.

---

## **4\. 핵심 가치 요약 (The KNUL Pillars v1.5.0)**

| 가치 | 설명 | 기술적 실현 |
| :---- | :---- | :---- |
| **Zero-copy I/O** | 데이터 복사 없는 초고속 전송 | Deno FFI \+ Shared Memory Pointer |
| **Protocol Sovereignty** | 네트워크 스택 완전 통제 | Hyper \+ Quinn 통합 Rust 커널 |
| **Deterministic Link** | 컨텍스트가 보장된 통신 경로 | 헤더 기반 Context 추적 및 명시적 주입 |

---