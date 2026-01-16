# **📑 [Krepis Base Spec 007 A] AI 군단 아키텍처 및 실시간 개입 프로토콜 (v1.6.0)**

**버전:** v1.6.0 (Autonomous Intervention & Human-in-the-loop)
**상태:** 최종 확정 (Finalized)
**핵심 변경 사항:** Self-Correction 임계치 정의, 에러 데이터 패키징 규격, 인간 개입 시점 명시

---

## **1. 실시간 자율 교정 프로토콜 (Self-Correction Protocol)**

### **1.1 Self-Correction 루프 및 임계치**

Atomic Executor(Worker)가 수행하는 '작성-테스트' 루프는 무한 루프에 빠지지 않도록 엄격한 임계치를 갖습니다.

* **[Step 1] Sub-Level Loop (최대 3회):** - Atomic Executor가 코드를 수정하고 Recursive CI를 실행합니다.
* 3회 연속 실패 시, 해당 작업은 즉시 중단되며 **'에러 데이터 패키지'**가 생성됩니다.


* **[Step 2] Expert-Level Intervention (1회):**
* **SovereignArchitect**가 패키지를 전달받아 아키텍처 결함이나 도메인 특화 문제를 분석합니다.
* SovereignArchitect의 가이드라인이 포함된 새로운 프롬프트가 Atomic Executor에게 하달되어 마지막 1회의 교정을 시도합니다.


* **[Step 3] Master-Level Escalation:** - Expert 개입 후에도 실패 시, **LegionMaster**가 Task의 분할 자체가 잘못되었는지 판단하여 Task 재설계 또는 포기를 결정합니다.

### **1.2 에러 데이터 패키징 규격 (Forensic Packet)**

자율 교정을 위해 AI에게 전달되는 데이터는 다음 형식을 준수해야 합니다.

| 필드명 | 내용 | 용도 |
| --- | --- | --- |
| **Runtime Snapshot** | [Spec-Dev-002]의 `ResourceSnapshot` | 리소스 부족 유무 판단 (OOM, Timeout 등) |
| **Logic Trace** | 실패 지점의 V8 Stack Trace 및 변수 덤프 | 논리적 결함 위치 특정 |
| **Recursive Diff** | 1~3차 수정 시도 시의 코드 변경 이력(Diff) | 반복되는 실수 패턴 분석 및 회피 |
| **Context Integrity** | 호출 당시의 `KrepisContext` 메타데이터 | 권한 부족이나 잘못된 테넌트 설정 확인 |

---

## **2. Human-in-the-loop (인간 개입 거버넌스)**

AI 군단이 자율적으로 해결할 수 없는 **'결정적 순간'**에는 반드시 인간 아키텍트의 승인 또는 개입이 필요합니다.

### **2.1 인간 개입의 정의 (Decision Thresholds)**

1. **Critical Safety Violation:** AI가 생성한 로직이 커널의 보안 정책(Sandbox Escape 시도 등)을 3회 이상 위반할 때.
2. **Infrastructure Cost Spike:** "USE" 기능을 통한 구축 시, 예상 비용이 유저가 설정한 예산 범위를 20% 초과할 때.
3. **Master-Level Deadlock:** LegionMaster가 Task 분할 및 재설계를 5회 이상 반복하며 결과물을 내지 못하는 '추론 루프'에 빠졌을 때.
4. **Ambiguous Intent:** 유저의 요구사항이 상충되어(예: "최고의 보안과 최저의 비용") AI가 우선순위를 결정할 수 없을 때.

### **2.2 개입 인터페이스: The Sovereign Console**

* **Intervention Signal:** 위 상황 발생 시 시스템은 아키텍트에게 푸시 알림을 보냅니다.
* **Decision Support:** AI는 현재까지의 시도 내역과 **"왜 인간의 개입이 필요한지"**에 대한 요약 보고서를 제출합니다.
* **Override & Resume:** 인간이 로직을 직접 수정하거나 우선순위를 결정해주면, AI 군단은 그 지점부터 다시 자율 실행을 재개합니다.

---

## **3. 런타임 자율 치유 (Sovereign Sentry) 워크플로우**

배포 후 런타임에서 발생하는 장애에 대한 처리 절차입니다.

1. **Detection:** 커널의 Watchdog이 실행 중단 또는 에러를 감지합니다.
2. **Analysis:** **SovereignArchitect(Sentry 모드)**가 에러 패키지를 즉시 분석합니다.
3. **Shadow Validation:** AI가 핫패치 코드를 생성하고, 실제 트래픽의 복사본(Shadow)을 통해 가상 환경에서 검증합니다.
4. **Zero-Inertia Deployment:** 검증 성공 시, 중단 없이 새로운 Isolate로 교체 배포합니다. (실패 시 인간 아키텍트 에스컬레이션)

---

## **4. 비즈니스 모델과의 연동 (Tier-based AI)**

* **ULTRA/ENTERPRISE:** 위 모든 자율 치유 및 핫패치 프로세스가 실시간(Real-time)으로 작동합니다.
* **PRO:** 자율 치유 시도 전 인간 아키텍트의 승인 과정을 반드시 거쳐야 합니다. (준-자율)

---