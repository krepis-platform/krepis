# **📑 \[Krepis-Spec-006\] Application Bootstrapper Specification (v1.1.0)**

**버전:** v1.1.0 (Lifecycle Hooks & Graceful Shutdown 확장)

**상태:** Final Draft

**모듈명:** @krepis/core/bootstrap

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Deterministic Startup:** 모든 모듈의 초기화 순서를 결정론적으로 관리하여 예기치 못한 레이스 컨디션을 방지합니다.  
2. **Fail-Fast on Start:** 필수 설정 누락이나 의존성 그래프 오류가 있다면 요청을 받기 전(Startup 단계)에 즉시 종료합니다.  
3. **Graceful Resilience:** 종료 신호 수신 시 진행 중인 작업을 안전하게 완료하고 자원을 해제하여 데이터 무결성을 보장합니다.  
4. **Observability by Default:** 부팅 과정의 모든 단계를 명확히 로깅하여 운영 가시성을 확보합니다.

---

## **Ⅱ. 핵심 인터페이스: Lifecycle Hooks**

각 모듈이나 서비스가 부트스트래퍼의 특정 단계에 개입할 수 있도록 표준 인터페이스를 제공합니다.

TypeScript

export interface IOnModuleInit {  
  /\*\* 모든 모듈이 로드된 후, DI 컨테이너가 생성되기 직전 실행 \*/  
  onModuleInit(): Promise\<void\> | void;  
}

export interface IOnApplicationBootstrap {  
  /\*\* 서버가 리스닝을 시작하기 직전 실행 (DB 연결 등 인프라 준비) \*/  
  onApplicationBootstrap(): Promise\<void\> | void;  
}

export interface IOnApplicationShutdown {  
  /\*\* 프로세스 종료 신호 시 실행 (자원 정리, 커넥션 종료) \*/  
  onApplicationShutdown(signal?: string): Promise\<void\> | void;  
}

---

## **Ⅲ. 부트스트래퍼 실행 프로세스 (The Flow)**

1. **Initialize Phase:**  
   * 환경 변수 및 설정 파일 검증 (Zod 기반 Schema Check).  
   * 등록된 모든 IOnModuleInit 훅 실행.  
2. **Assemble Phase:**  
   * ServiceCollection을 빌드하여 ServiceProvider 생성.  
   * **DI Graph Audit:** 모든 싱글톤 객체의 의존성 누락 여부 전수 검사.  
3. **Bootstrap Phase:**  
   * 등록된 모든 IOnApplicationBootstrap 훅 실행 (DB 커넥션 풀 활성화, 메시지 브로커 연결).  
   * **Health Check:** 핵심 인프라 가용성 최종 확인.  
4. **Ready Phase:**  
   * 진입점(HTTP/gRPC/CLI) 리스닝 시작 및 부팅 배너 출력.

---

## **Ⅳ. 상세 구현 명세 (Technical Detail)**

### **1\. Graceful Shutdown 엔진**

종료 신호 감지 시 파이프라인 중단 및 자원 해제를 관리합니다.

TypeScript

export class KrepisBootstrapper {  
  private async handleShutdown(signal: string) {  
    this.logger.info(\`Received ${signal}. Starting graceful shutdown...\`);  
      
    // 1\. 새로운 요청 유입 차단 (Listener Stop)  
    await this.entryPoint.stop();

    // 2\. 진행 중인 파이프라인 작업 대기 (Graceful Wait)  
    // Spec-003의 AbortSignal 전파를 통해 장기 작업 종료 유도

    // 3\. 역순으로 Shutdown 훅 실행 (자원 해제)  
    for (const hook of this.shutdownHooks.reverse()) {  
      await hook.onApplicationShutdown(signal);  
    }

    this.logger.info("Graceful shutdown completed.");  
    process.exit(0);  
  }  
}

### **2\. Config Validation (Fail-Fast)**

애플리케이션이 뜨기 전 '설정의 무결성'을 보장합니다.

TypeScript

export class ConfigValidator {  
  static validate\<T\>(schema: ZodSchema\<T\>, config: any): T {  
    const result \= schema.safeParse(config);  
    if (\!result.success) {  
      console.error("❌ Invalid Configuration:", result.error.format());  
      process.exit(1); // 즉시 종료  
    }  
    return result.data;  
  }  
}

---

## **Ⅴ. 부트스트랩 예시 (Usage)**

TypeScript

async function bootstrap() {  
  const app \= await KrepisFactory.create(AppModule, {  
    logger: new KrepisLogger(),  
    abortTimeout: 5000, // 종료 대기 시간 5초  
  });

  // 전역 파이프라인 설정  
  app.useGlobalBehaviors(  
    new ContextBridgeBehavior(),  
    new TransactionBehavior()  
  );

  await app.start(3000);  
}

---

## **Ⅵ. 기대 효과 (KPI)**

1. **신뢰성(Reliability):** 잘못된 설정이나 인프라 장애 상태에서 서버가 구동되는 "좀비 프로세스" 방지.  
2. **데이터 정합성:** 갑작스러운 종료 시에도 UoW와 결합된 Graceful Shutdown을 통해 데이터 손실 0%.  
3. **운영 효율성:** 표준화된 Lifecycle 훅을 통해 모듈 간의 결합도를 낮추고 유지보수 용이성 향상.

---
