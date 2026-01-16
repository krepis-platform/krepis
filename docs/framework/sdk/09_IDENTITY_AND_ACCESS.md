# **📑 \[Krepis-Spec-012\] Identity & Access Management Module (v1.1.0)**

**버전:** v1.1.0 (Tenancy, ABAC & Real-time Revocation 확장)

**상태:** Final Draft

**모듈명:** @krepis/auth

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Zero-Trust Identity:** 모든 요청은 유효한 Identity를 증명해야 하며, 토큰이 있더라도 실시간 보안 스탬프 검증을 통해 유효성을 재확인합니다.  
2. **Tenant Isolation by Design:** 모든 인증 데이터와 권한 체크는 테넌트(TenantId)를 기반으로 격리되어 데이터 혼입을 원천 차단합니다.  
3. **Policy-Based Access Control (PBAC):** 역할(Role) 기반을 넘어, 요청자/자원/환경의 속성을 결합한 정교한 정책 인가를 수행합니다.  
4. **Privacy & Security First:** 개인정보(Claims)는 토큰에 최소화하여 담고, 서버 사이드에서 필요한 시점에만 보충(Hydration)하여 노출을 방지합니다.

---

## **Ⅱ. 핵심 도메인 모델 및 테넌트 격리**

### **1\. Tenant-Aware User Aggregate**

TypeScript

export class User extends AggregateRoot {  
  readonly id: string;  
  readonly tenantId: string;       // 다중 테넌트 식별자  
  username: string;  
  securityStamp: string;           // 비밀번호 변경/로그아웃 시 갱신  
    
  // 권한 및 상태  
  roles: string\[\] \= \[\];  
  claims: Claim\[\] \= \[\];  
  status: UserStatus;              // ACTIVE, LOCKED, PENDING  
    
  /\*\* 보안 스탬프 갱신: 모든 기존 세션 무효화 \*/  
  updateSecurityStamp(): void {  
    this.securityStamp \= crypto.randomUUID();  
    this.addEvent(new SecurityStampChangedEvent(this.id, this.securityStamp));  
  }  
}

---

## **Ⅲ. 실시간 보안 및 토큰 관리**

### **1\. Security Stamp & Deny-list (Redis)**

Stateless한 JWT의 단점을 보완하기 위해 리포지토리 레이어와 연동된 실시간 검증을 수행합니다.

* **Blacklisting:** 로그아웃된 jti(JWT ID)를 토큰 만료 시까지 Redis에 보관.  
* **Stamp Validation:** 중요 작업 시 DB/Cache의 securityStamp와 토큰 내 스탬프를 대조.

### **2\. Refresh Token Rotation**

재사용 방지(Reuse Detection)를 포함한 로테이션 전략을 적용합니다. 기존 리프레시 토큰으로 새 토큰을 요청하면 이전 모든 토큰 체인을 무효화합니다.

---

## **Ⅳ. 통합 파이프라인 보안 레이어**

### **1\. AuthenticationBehavior (Identity Hydration)**

토큰에서 최소 정보만 추출한 후, 컨텍스트에 풍부한 Identity 정보를 주입합니다.

TypeScript

export class AuthenticationBehavior implements IPipelineBehavior {  
  async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
    const principal \= await this.tokenService.decode(ctx.request.token);  
      
    if (principal) {  
      // 1\. 필수 컨텍스트 설정  
      ctx.context.set(AUTH\_USER\_ID, principal.sub);  
      ctx.context.set(AUTH\_TENANT\_ID, principal.tid);  
        
      // 2\. Deny-list 및 Security Stamp 검증 (Interval 기반 최적화)  
      if (await this.securityService.isRevoked(principal)) {  
        return Fail(new UnauthorizedError("Session has been revoked."));  
      }  
    }  
    return await next();  
  }  
}

### **2\. AuthorizationBehavior (ABAC & Policy)**

속성 기반 인가를 처리하기 위해 Specification과 정책 평가기를 결합합니다.

TypeScript

export class AuthorizationBehavior implements IPipelineBehavior {  
  async handle(ctx: PipelineContext, next: NextPipe\<any\>) {  
    const policyName \= ctx.request.metadata?.policy;  
    if (\!policyName) return await next();

    // 1\. 현재 컨텍스트와 요청 데이터를 기반으로 정책 평가  
    const result \= await this.policyEvaluator.authorize(policyName, {  
      user: ctx.context.get(AUTH\_USER),  
      resource: ctx.request.body, // 대상 리소스 속성  
      env: { ip: ctx.request.ip, time: new Date() }  
    });

    if (\!result.satisfied) return Fail(new ForbiddenError(result.reason));  
    return await next();  
  }  
}

---

## **Ⅴ. 고도화된 권한 정책 예시**

### **1\. 상속 가능한 복합 정책 (Composite Policy)**

TypeScript

authBuilder.addPolicy('SensitiveOperation', policy \=\> {  
  policy.requireAuthenticated()  
        .requireTenantMatch()  
        .requireClaim('mfa', 'verified') // MFA 인증 필수  
        .addRequirement(new SecurityStampAgeRequirement({ maxMinutes: 30 })); // 최근 30분 내 스탬프 확인  
});

---

## **Ⅵ. 기대 효과 (KPI)**

1. **데이터 격리(Isolation):** TenantId 강제 주입을 통해 테넌트 간 데이터 노출 사고 0% 지향.  
2. **보안 반응성(Responsiveness):** Security Stamp 메커니즘을 통해 계정 탈취 시 즉각적인(Real-time) 전역 로그아웃 구현.  
3. **유연한 정책(Flexibility):** 코드 수정 없이 정책 정의만으로 "주말에는 관리자도 결제 승인 불가"와 같은 정교한 ABAC 구현 가능.

---
