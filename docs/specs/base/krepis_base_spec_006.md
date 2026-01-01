# **📑 \[Krepis Base Spec-006\] 프레임워크 이원화 전략 상세 명세 (v1.5.0)**

버전: v1.5.0 (The Unified Symmetry)

분류: 런타임 전략 및 개발 워크플로우

## **1\. 개요 (Executive Summary)**

Krepis는 동일한 비즈니스 로직 코드베이스 위에서 \*\*엔진의 교체(Kernel Swapping)\*\*만으로 성능과 개발 편의성을 모두 잡는 이원화 전략을 채택합니다. 모든 환경은 **Deno 런타임**으로 통일되어 환경 파편화를 방지하며, 개발자는 필요에 따라 엔진의 심장만을 교체합니다.

## **2\. 이원화 엔진 정의 및 역할**

### **① Krepis Standard (Deno-TS Simulator)**

* **기술 스택:** Pure TypeScript (Deno) / TS Mock Kernel  
* **특징:** Rust 네이티브 바이너리 없이 실행되는 **'논리 검증용'** 엔진.  
* **작동 원리:** Explicit Context 및 Trinity 패턴을 TS 인터페이스로 구현하여, 실제 네이티브 가속 없이 비즈니스 로직의 정합성만을 체크합니다.  
* **장점:** \* 별도의 컴파일 과정이 없어 개발 생산성 극대화.  
  * 에러 발생 시 완벽한 TS 스택 트레이스 제공.  
  * 저사양 로컬 환경 및 CI/CD 파이프라인 최적화.

### **② Krepis Turbo (Sovereign Native Engine)**

* **기술 스택:** Rust (Native) \+ Deno FFI \+ Hyper-Pingora  
* **특징:** 성능 병목 구간을 Rust 네이티브 커널이 직접 지배하는 **'프로덕션급'** 엔진.  
* **작동 원리:** \[Spec-002\]의 KNUL 통신과 \[Spec-004\]의 Zero-copy 브릿지가 활성화되어 하드웨어 자원을 극한으로 사용합니다.  
* **장점:** \* CPU/메모리 효율의 임계치 돌파.  
  * 비즈니스 로직 보호(Native 은닉) 및 초저지연 네트워킹.  
  * 명시적 컨텍스트를 네이티브 레벨에서 강제 격리 및 관리.

---

## **3\. 핵심 운영 전략: "Zero-Inertia Switching"**

### **3.1 단일 코드베이스 정책 (Single-Source Truth)**

사용자가 작성하는 Entity, UseCase, Repository는 엔진 모드에 관계없이 **100% 동일**합니다.

TypeScript

// krepis.config.ts  
export const config \= {  
  // 모드 전환 시 코드 수정 없음, 엔진 레이어만 교체됨  
  kernel: Deno.env.get("ENV") \=== "production" ? "turbo" : "standard",  
  port: 3000,  
};

### **3.2 결정적 인터페이스 브릿지 (Deterministic Interface)**

* **Standard 모드:** TS 기반의 가상 컨텍스트 객체를 생성하여 주입.  
* **Turbo 모드:** Rust 커널이 생성한 네이티브 메모리 포인터를 래핑한 컨텍스트 객체를 주입.  
* **결과:** 개발자는 주입받는 ctx가 TS 가상 객체인지 Rust 네이티브 핸들인지 알 필요 없이 동일한 비즈니스 로직을 수행합니다.

---

## **4\. 로드맵에 따른 단계별 구현 (Kernel Evolution)**

* **Phase 1 (Mock-up):** 모든 핵심 명세를 TS로 구현한 Standard 엔진 완성. 9대 모듈 표준 가이드 배포.  
* **Phase 2 (Native Fusion):** Turbo 엔진(Hyper-Pingora 기반)을 Deno FFI로 결합. 고부하 I/O 작업부터 네이티브로 이관.  
* **Phase 3 (Sovereign Completion):** 모든 인프라 로직(로그, 보안, 통신)이 Turbo 엔진에서 네이티브로 구동되는 완전체 완성.

---

## **5\. 기대 효과 및 비전**

1. **학습 곡선의 획기적 단축:** "성능은 Rust급이지만, 개발은 TS처럼"이라는 약속을 지킵니다.  
2. **개발-운영 환경의 대칭성:** 런타임(Deno)을 통일함으로써 Node.js 환경에서 발생하던 "내 컴퓨터에선 되는데 서버에선 안 돼요" 문제를 근본적으로 해결합니다.  
3. **유연한 스케일링:** 서비스 초기에는 Standard로 빠르게 런칭하고, 트래픽 급증 시 설정 변경만으로 Turbo의 성능을 즉시 수혈받을 수 있습니다.

---
