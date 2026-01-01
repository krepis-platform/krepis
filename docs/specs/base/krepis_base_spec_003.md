# **📑 \[Krepis Base Spec-003\] AI 군단 아키텍처 및 프랙탈 지능 명세서**

버전: v2.0.0 (The Fractal Legion & USE System)

분류: AI 아키텍처, 지능형 오케스트레이션, 자율 구축 프로세스

## **1\. 프랙탈 지능 구조 (Fractal Legion Architecture)**

단일 모델의 한계를 극복하기 위해 AI 에이전트를 계층화하고, **Explicit Context**를 통해 명령 체계를 통일합니다.

### **1.1 계층별 역할 정의 (Legion Hierarchy)**

* **Global Master AI (The General):** 유저의 요구사항을 해석하고, 전체 시스템 아키텍처를 설계하며 **Super Micro Task**로 작업을 분해합니다.  
* **Expert AI (The Officers):** 보안(Sentinel), 성능(Optimizer), 구조(Architect) 전문가로 구성되어 상위 설계를 검수하고 하위 작업을 감독합니다.  
* **Atomic Executor (The Soldiers):** 가장 가볍고 빠른 모델로 구성되어, 분할된 Micro Task를 작성하고 **Recursive CI** 루프를 수행합니다.

### **1.2 지휘 체계: Recursive Context Propagation**

* **의도 보존:** Master가 생성한 ctx는 하위 계층으로 갈수록 구체적인 제약 사항이 추가(Decoration)되며, 말단 Executor는 ctx에 명시된 범위 내에서만 코드를 작성할 수 있습니다.  
* **역방향 검증:** Executor가 완료한 작업은 역순으로 Expert와 Master의 검증을 거쳐 최종적으로 AiDev 브랜치에 통합됩니다.

## **2\. "USE" 자율 구축 엔진 (Autonomous Construction)**

마켓플레이스의 핵심 서비스인 "USE"를 구동하는 AI의 자율 행동 강령입니다.

### **2.1 상방향 문답 (Exploratory Blueprinting)**

* **질문 주도 설계:** AI는 유저의 모호한 요구사항에 대해 역으로 질문을 던져 **Architecture Spec**을 확정합니다.  
* **명세서 주입:** 확정된 Spec과 유저가 업로드한 문서(PDF/Swagger/MD)를 결합하여 **Explicit Context**의 소스로 삼습니다.

### **2.2 결정적 생성 및 가상 검증 (Build & Simulate)**

* **Zero-Defect Build:** 프랙탈 군단이 가동되어 전 레이어 80% 이상의 커범리지를 가진 무결점 코드를 생성합니다.  
* **Digital Twin Simulation:** 배포 전 가상 컨테이너에서 임계치 이상의 트래픽을 투입하여 성능 지표(P99 Latency)를 리포팅합니다.

## **3\. Super Micro Tasking & Recursive CI**

AI가 생성하는 코드의 품질을 보장하기 위한 원자 단위 작업 공정입니다.

### **3.1 원자적 작업 분할 (Atomic Tasking)**

* 모든 작업은 **단일 파일 혹은 단일 함수 단위**로 쪼개집니다. 이는 AI의 컨텍스트 집중도를 높이고 환각(Hallucination)을 원천 차단합니다.

### **3.2 자가 교정 루프 (Self-Correction Loop)**

1. **Generation:** Sub AI가 ctx를 기반으로 코드를 작성합니다.  
2. **Native Test:** Rust 커널이 즉시 컴파일 및 deno test를 실행합니다.  
3. **Log Analysis:** 실패 시 에러 로그를 분석하여 AI가 스스로 코드를 수정합니다.  
4. **Final Gate:** 3회 이상 실패 시 Expert AI가 개입하여 로직을 재설정합니다.

## **4\. 데이터 주권 및 티어별 지능 정책**

플랜별로 투입되는 AI 군단의 등급과 보안 수준을 차등화합니다.

### **4.1 5단계 지능 배정 (Tiered Intelligence)**

* **FREE/PLUS:** 범용 경량 모델 기반의 가이드 및 소규모 생성.  
* **PRO/ULTRA:** **Codestral/Mistral Large** 등 정예 모델 투입 및 **Sovereign Sentry(자율 치유)** 가동.  
* **ENTERPRISE:** 기업 전용 격리 모델(Air-gapped) 및 커스텀 파인튜닝(SFT) 제공.

### **4.2 비식별 AST 전송 (Privacy-Preserving)**

* **AST 기반 통신:** 소스코드 원본 대신 구조 정보인 AST만 추출하여 전송합니다. 비즈니스 로직의 리터럴은 **Deterministic Masking** 처리되어 IP(지식재산권) 유출을 방지합니다.

## **5\. 핵심 가치 요약 (The Intelligent Pillars v2.0.0)**

| 가치 | 설명 | 기술적 실현 |
| :---- | :---- | :---- |
| **Fractal Authority** | 계층적 지휘 체계를 통한 무결성 확보 | Master-Expert-Sub AI 계층 구조 |
| **Recursive Integrity** | 테스트를 통과할 때까지 자가 수정 | Native Test 기반 Recursive CI 루프 |
| **Autonomous Delivery** | 명세서 입력만으로 완성된 시스템 제공 | "USE" 자율 구축 엔진 및 시뮬레이션 |
| **Data Sovereignty** | 플랜별 완벽한 데이터 격리 및 보호 | Rust 기반 데이터 고립 및 비식별 AST |

---