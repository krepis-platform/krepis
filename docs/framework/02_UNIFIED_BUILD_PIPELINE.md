# **📑 \[Krepis\] 1\. 통합 빌드 및 자산 관리 상세 명세 (v1.5.0)**

**버전: v1.5.0 (Sovereign Build Engine)**

**분류: 빌드 아키텍처 및 CI/CD 워크플로우**

## **1.1 아티팩트 및 FFI 바인딩 관리 (Artifacts & FFI)**

* **바이너리 위치 (Native Kernel): Rust 빌드 결과물(.so, .dll, .dylib)은 crates/krepis-kernel/target/release에서 관리되며, 배포 시 packages/core/bin으로 플랫폼별(target triple) 식별자와 함께 아카이빙됩니다.**  
* **FFI 정의 자동 동기화: NAPI-RS 대신 Deno FFI를 사용하므로, Rust의 struct와 fn을 분석하여 Deno가 이해할 수 있는 UnsafePointer 기반의 \*\*bindings.ts\*\*를 자동 생성(Codegen)합니다. 이를 통해 TS 레이어는 런타임에 네이티브 심볼을 타입 안전하게 호출합니다.**

[See Also](../framework/kernel/04_FFI_MEMORY_SAFETY.md)

## **1.2 Sovereign 태스크 의존성 설계 (Dependency Graph)**

**Turborepo 대신 \*\*deno task\*\*와 \*\*cargo\*\*의 고유 기능을 조합하여 병렬성과 결정성을 확보합니다.**

* **빌드 순서:**  
  1. **cargo build \--package krepis-ffi: FFI 인터페이스용 메타데이터 추출.**  
  2. **deno task codegen: 추출된 메타데이터를 기반으로 TS 바인딩 코드 생성.**  
  3. **cargo build \--package krepis-kernel: 최종 네이티브 커널 바이너리 생성.**  
  4. **deno check packages/core: 생성된 바인딩과 비즈니스 로직의 타입 정합성 최종 검증.**  
* **효율화: Deno의 deno.json 캐싱과 Cargo의 증분 빌드를 결합합니다. 변경이 없는 컴포넌트는 재연산 없이 즉시 통과됩니다.**

## **1.3 로컬 개발 환경 (Sovereign DX Loop)**

* **Watch Mode 통합: cargo watch와 deno task dev \--watch를 상호 운용합니다.**  
* **동작 방식: Rust 커널 수정 시 컴파일이 완료될 때까지 Deno는 기존 바이너리를 유지하거나 \*\*Standard 모드(TS Simulator)\*\*로 즉시 스위칭하여 개발 중단(Inertia)을 방지합니다. 네이티브 컴파일이 완료되면 Deno 런타임은 동적 임포트(Dynamic Import)를 통해 새 바이너리를 리로드합니다.**

## **1.4 CI/CD 및 멀티 플랫폼 전략**

* **멀티 플랫폼 빌드: GitHub Actions의 Matrix Build를 통해 Linux(GNU/Musl), macOS(Intel/Apple Silicon), Windows 환경에서 병렬 빌드합니다.**  
* **바이너리 무결성: 모든 플랫폼별 바이너리에 대해 SHA-256 체크섬을 생성하고, 이를 packages/core의 메니페스트 파일에 기록합니다. 런타임 로드 시 커널이 스스로의 해시를 대조하여 위변조를 차단합니다.**

## **1.5 빌드 설정 공유 (Build-time Context)**

* **환경 변수 제어: deno.json의 env 설정과 Cargo의 \[features\] 플래그를 동기화합니다.**  
* **Optimization Profile: 개발 단계에서는 Debug 프로파일로 빌드 속도를 확보하고, 배포 단계에서는 LTO (Link Time Optimization)를 활성화한 Release 프로파일을 사용하여 네이티브 성능을 극대화합니다.**

---

## **🛠️ 고도화된 deno.json 태스크 명세 (예시)**

**기존 turbo.json의 복잡한 설정을 Deno 네이티브 방식으로 단순화하고 명확하게 정의합니다.**

**JSON**

```json
{  
    "tasks": {  
    "codegen": "deno run \-A tools/codegen/main.ts",  
    "build:kernel": "cargo build \--release \--package krepis-kernel",  
    "build:all": "deno task codegen && deno task build:kernel && deno check packages/core/mod.ts",  
    "dev": "ENV=development deno run \-A \--watch packages/core/main.ts",  
    "test:native": "cargo test",  
    "test:ts": "deno test \-A packages/core/tests/",  
    "test:all": "deno task test:native && deno task test:ts"  
  },  
  "lint": {  
    "rules": {  
      "tags": \["recommended"\]  
    }  
  },  
  "fmt": {  
    "useTabs": false,  
    "lineWidth": 100  
  }  
}
```
---
