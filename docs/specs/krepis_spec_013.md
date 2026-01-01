# **📑 \[Krepis-Spec-013\] Unified Configuration Module (v1.2.1)**

**버전:** v1.2.1 (Hot-reload, Monitor & Post-processor 확장)

**상태:** Final Draft

**모듈명:** @krepis/config

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Source Immutability & Overriding:** 원본 소스는 수정하지 않으며, 계층적 구조를 통해 상위 우선순위의 설정이 하위 설정을 덮어씁니다.  
2. **Strict Type-Safety:** Zod 스키마를 통한 강한 타입 검증을 수행하며, 검증 실패 시 부트스트랩 단계에서 즉시 중단(Fail-fast)합니다.  
3. **Change Propagation:** 런타임에 설정이 변경될 경우(Hot-reload), 이를 구독 중인 서비스들에게 안전하게 알림을 전파합니다.  
4. **Derived Value Resolution:** 단순 로드를 넘어, 로드된 값들을 조합하여 새로운 값을 생성(Post-processing)할 수 있어야 합니다.

---

## **Ⅱ. 핵심 데이터 구조 및 인터페이스**

### **1\. IOptionsMonitor (동적 감시자)**

싱글톤 서비스가 최신 설정을 실시간으로 반영할 수 있게 돕는 인터페이스입니다.

TypeScript

export interface IOptionsMonitor\<T\> {  
  /\*\* 현재 활성화된 최신 설정 값 \*/  
  readonly current: T;  
  /\*\* 설정 변경 시 실행될 콜백 등록 \*/  
  onChange(listener: (updated: T) \=\> void): IDisposable;  
}

### **2\. Config Post-Processor (계산된 설정)**

병합이 완료된 후 최종적으로 데이터를 가공하는 로직입니다.

TypeScript

export interface IConfigPostProcessor {  
  /\*\* \* 병합된 전체 Raw Config를 인자로 받아 가공   
   \* 예: host와 port를 결합하여 connectionString 생성  
   \*/  
  process(rawConfig: Record\<string, any\>): Record\<string, any\>;  
}

---

## **Ⅲ. 상세 구현 전략**

### **1\. 계층적 로딩 및 조건부 빌더**

환경(Environment)에 따라 로더를 유연하게 구성합니다.

TypeScript

const builder \= KrepisFactory.createBuilder();

builder.configureConfig((config) \=\> {  
  config  
    .addJsonFile('appsettings.json')  
    .addIf(process.env.NODE\_ENV \=== 'production', (c) \=\>   
       c.addAzureKeyVault({ /\* ... \*/ })  
    )  
    .addEnvironmentVariables()  
    .addPostProcessor((raw) \=\> ({  
      ...raw,  
      db: { ...raw.db, url: \`postgresql://${raw.db.user}:${raw.db.pass}@${raw.db.host}\` }  
    }));  
});

### **2\. Secret Masking & Security**

민감한 정보가 로깅 시스템에 노출되지 않도록 처리합니다.

---

## **Ⅳ. 런타임 동적 갱신 메커니즘 (Hot-Reload)**

외부 저장소(Vault 등)나 파일 시스템의 변경을 감지하여 애플리케이션 상태를 동기화합니다.

TypeScript

// infrastructure/config/ConfigMonitor.ts  
export class DatabaseService {  
  constructor(  
    private readonly config: IOptionsMonitor\<DatabaseConfig\>  
  ) {  
    // 설정 변경 감지 시 커넥션 풀 재설정  
    this.config.onChange((newConfig) \=\> {  
      this.reconnect(newConfig);  
    });  
  }

  private reconnect(config: DatabaseConfig) {  
    this.logger.info("Database configuration updated. Reconnecting...");  
    // ... logic  
  }  
}

---

## **Ⅴ. 정적 타입 검증 및 에러 리포팅 (Zod)**

설정 로드 직후 스키마 검증을 통해 부팅 가시성을 확보합니다.

TypeScript

// @krepis/config 내부 로직  
const result \= schema.safeParse(mergedRawData);  
if (\!result.success) {  
  throw new ConfigValidationException(  
    "Configuration check failed at startup.",  
    result.error.issues // 상세 미충족 항목(path, expected, actual) 포함  
  );  
}

---

## **Ⅵ. 기대 효과 (KPI)**

1. **무중단 운영(Zero-Downtime):** 보안 인증서나 API 키 변경 시 재시작 없이 런타임에 설정을 반영하여 가용성 향상.  
2. **환경 일관성:** 로컬(.env), 스테이징(YAML), 운영(HSM) 간의 코드 베이스 일치율 100% 달성.  
3. **보안 사고 예방:** 로깅 모듈과의 통합 마스킹을 통해 민감 정보 노출 사고를 근본적으로 차단.

---
