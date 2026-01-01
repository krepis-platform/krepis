# **📑 \[Krepis\] 2\. 언어별 코드 품질 및 스타일 가드 상세 명세 (v1.5.0)**

**버전: v1.5.0 (Sovereign Quality Standard)**

**분류: 코드 스타일, 정적 분석 및 아키텍처 규범**

## **2.1 TypeScript 품질 표준 (The Governance)**

### **\[2.1.1\] 명명 및 Trinity 선언 규칙**

* **인터페이스 (I-Prefix): 모든 추상 인터페이스는 I 접두사를 사용합니다 (예: IUserRepository). 이는 구체 클래스(Adapter)와 추상화(Domain)를 시각적으로 분리하여 헥사고날 아키텍처의 의존성 역전(DIP)을 명확히 시각화합니다.**  
* **Architecture Decorators: Trinity 패턴의 소속을 명시하기 위해 다음 데코레이터를 강제합니다.**  
  * **@DomainEntity(), @ApplicationService()**  
  * **@InfraAdapter(), @ContextBridge()**  
* **Naming: 에넘(Enum)은 PascalCase, 상수는 UPPER\_SNAKE\_CASE를 준수합니다.**

### **\[2.1.2\] Deno 기반 엄격도 및 레이어 가드**

* **Zero Any Policy: any 사용 시 deno lint에서 에러를 발생시킵니다. 데이터 구조를 모를 경우 unknown을 사용하고 명시적 Type Guard(isType)를 거쳐야 합니다.**  
* **Sovereign Import Guard: deno\_graph를 활용한 커스텀 린트 규칙을 통해 Domain → Infra 방향의 임포트를 원천 차단합니다. 모든 인프라 참조는 반드시 I\-인터페이스를 통한 의존성 주입으로만 이루어져야 합니다.**

## **2.2 Rust 품질 표준 (The Performance)**

### **\[2.2.1\] 안전성 및 린트 수준 (Crate Integrity)**

* **Clippy (Strict Pedantic): \#\!\[deny(clippy::all, clippy::pedantic)\]를 크레이트 최상단에 선언합니다. 특히 missing\_errors\_doc, must\_use\_candidate 등 성능과 안정성에 직결되는 규칙을 강화합니다.**  
* **Unsafe Sovereignty: unsafe 블록 사용 시 반드시 // SAFETY: \<논리적 근거\> 주석을 병기해야 합니다. 근거가 불충분하거나 누락된 경우 CI 단계에서 빌드를 중단합니다.**

### **\[2.2.2\] 에러 브릿지 및 가시성 제어**

* **Error Mapping: Rust의 thiserror를 활용하여 생성된 에러는 Deno FFI 브릿지에서 TS의 KrepisNativeException 클래스로 자동 변환됩니다.**  
* **Encapsulation: 모든 필드와 모듈은 pub(crate)를 기본값으로 하며, FFI를 통해 TS 레이어로 노출되는 인터페이스만 최소한으로 pub 선언합니다.**

## **2.3 공통 표준 및 통합 자동화 (The Integration)**

### **\[2.3.1\] 스타일 일관성 및 문서화**

* **FFI Case Mapping: Codegen 도구를 통해 Rust의 snake\_case 필드를 TS의 camelCase로 자동 변환합니다. 개발자는 각 언어의 고유 관례(Idiom)를 파괴하지 않고 코딩합니다.**  
* **Documentation Force: 모든 Public API는 JSDoc 또는 Rustdoc이 필수입니다. 누락 시 deno task check에서 경고가 아닌 에러를 발생시킵니다.**

### **\[2.3.2\] 코드 위생 및 위변조 방지**

* **TODO Debt Control: TODO 주석이 포함된 코드는 ENV=production 빌드 시 에러를 발생시킵니다. 기술 부채의 메인 브랜치 유입을 시스템적으로 차단합니다.**  
* **Apache-2.0 License Guard: 모든 소스 파일 상단에 라이선스 헤더가 없을 경우 커밋을 방지하는 pre-commit 스크립트를 Deno로 작성하여 배포합니다.**

---

## **🛠️ 품질 가드 구성 요약 (v1.5.0)**

| 구분 | TypeScript (Deno Lint/Fmt) | Rust (Clippy/Rustfmt) |
| :---- | :---- | :---- |
| **핵심 명명** | **I\-Interface, PascalCase Type** | **snake\_case Func, PascalCase Struct** |
| **엄격도** | **no-explicit-any, Strict: true** | **clippy::pedantic, Result\<T, E\> 강제** |
| **레이어 가드** | **Domain Isolation (Lint)** | **pub(crate) 기반 캡슐화** |
| **에러 처리** | **KrepisNativeException (TS)** | **thiserror / anyhow (Rust)** |
| **자동화 도구** | **deno task check** | **cargo clippy \--all-targets** |

---
