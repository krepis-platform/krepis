# **📑 \[Krepis-Spec-009\] Specification Pattern Specification (v1.1.0)**

**버전:** v1.1.0 (Async Evaluation & Expression Tree 확장)

**상태:** Final Draft

**모듈명:** @krepis/specification

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Unified Rule Source:** 하나의 명세 클래스가 메모리 검증(Validation), 데이터베이스 필터링(Query), 비즈니스 정책 평가(Policy)를 통합 관리합니다.  
2. **Universal Expression:** 특정 DB 문법에 종속되지 않는 표준 연산자 구조를 통해 플랫폼 이식성을 보장합니다.  
3. **Explainable Decision:** 단순한 성공/실패를 넘어 위반된 규칙, 현재 값, 기대 값 등의 정밀한 메타데이터를 제공합니다.  
4. **Async-Ready:** 외부 API 조회나 DB 정합성 체크가 필요한 비즈니스 규칙을 위해 비동기 평가를 기본 지원합니다.

---

## **Ⅱ. 핵심 데이터 구조 (Data Contract)**

### **1\. 표준 연산자 트리 (Criteria Expression)**

리포지토리 어댑터가 해석할 수 있는 중립적 쿼리 표현식입니다.

TypeScript

export type Operator \= 'eq' | 'neq' | 'gt' | 'gte' | 'lt' | 'lte' | 'in' | 'contains';

export interface ICriteria {  
  readonly field: string;  
  readonly operator: Operator;  
  readonly value: any;  
}

export type QueryCriteria \= ICriteria | { and: QueryCriteria\[\] } | { or: QueryCriteria\[\] } | { not: QueryCriteria };

### **2\. 정밀 평가 결과 (Detailed Result)**

TypeScript

export interface IEvaluationResult {  
  readonly satisfied: boolean;  
  readonly code: string;            // 예: 'MIN\_AGE\_VIOLATION'  
  readonly message: string;         // 템플릿 처리된 메시지  
  readonly params?: Record\<string, any\>; // { min: 20, actual: 18 }  
  readonly children?: IEvaluationResult\[\]; // AND/OR 조합 시 하위 결과  
}

---

## **Ⅲ. 상세 API 명세 (API Specification)**

### **1\. Base Specification (포트/인터페이스)**

TypeScript

export abstract class BaseSpecification\<T\> {  
  /\*\* 1\. 메모리 내 비동기 평가 (Validation/Policy용) \*/  
  abstract isSatisfiedBy(candidate: T): Promise\<boolean\> | boolean;

  /\*\* 2\. 상세 결과 반환 \*/  
  async evaluate(candidate: T): Promise\<IEvaluationResult\> {  
    const satisfied \= await this.isSatisfiedBy(candidate);  
    return {  
      satisfied,  
      code: this.constructor.name,  
      message: satisfied ? 'Success' : \`Specification ${this.constructor.name} not satisfied.\`,  
    };  
  }

  /\*\* 3\. DB 쿼리 변환 인터페이스 \*/  
  toQueryCriteria(): QueryCriteria {  
    return {} as QueryCriteria; // 필요 시 하위 클래스에서 오버라이드  
  }

  // 조합 메서드 (Fluent Interface)  
  and(other: BaseSpecification\<T\>): BaseSpecification\<T\> { return new AndSpecification(this, other); }  
  or(other: BaseSpecification\<T\>): BaseSpecification\<T\> { return new OrSpecification(this, other); }  
}

---

## **Ⅳ. 구현 전략 및 예시**

### **1\. 복합 명세 및 실패 추적 (Composite Logic)**

AndSpecification은 모든 조건을 검사하며, 실패한 모든 지점의 트리를 반환합니다.

TypeScript

export class AndSpecification\<T\> extends BaseSpecification\<T\> {  
  constructor(private left: BaseSpecification\<T\>, private right: BaseSpecification\<T\>) { super(); }

  async evaluate(candidate: T): Promise\<IEvaluationResult\> {  
    const \[leftRes, rightRes\] \= await Promise.all(\[  
      this.left.evaluate(candidate),  
      this.right.evaluate(candidate)  
    \]);

    return {  
      satisfied: leftRes.satisfied && rightRes.satisfied,  
      code: 'AND\_CONDITION',  
      message: 'Multiple conditions must be met',  
      children: \[leftRes, rightRes\]  
    };  
  }  
}

### **2\. 구체적 비즈니스 명세 (Prisma 연동 예시)**

TypeScript

export class UserAgeSpecification extends BaseSpecification\<User\> {  
  constructor(private readonly minAge: number) { super(); }

  isSatisfiedBy(user: User): boolean {  
    return user.age \>= this.minAge;  
  }

  toQueryCriteria(): QueryCriteria {  
    return { field: 'age', operator: 'gte', value: this.minAge };  
  }

  async evaluate(user: User): Promise\<IEvaluationResult\> {  
    const satisfied \= this.isSatisfiedBy(user);  
    return {  
      satisfied,  
      code: 'INVALID\_AGE',  
      message: \`User must be at least ${this.minAge} years old.\`,  
      params: { minAge: this.minAge, currentAge: user.age }  
    };  
  }  
}

---

## **Ⅴ. 기대 효과 및 결합 (Integration)**

1. **Repository 결합:** userRepo.find(new UserAgeSpecification(20)) 호출 시, 어댑터가 QueryCriteria를 읽어 즉시 WHERE age \>= 20 SQL을 생성합니다.  
2. **Pipeline 결합:** ValidationBehavior가 Command 객체를 명세에 대입하여 실패 시 상세한 에러 코드가 담긴 Result.fail()을 반환합니다.  
3. **Context 결합:** isSatisfiedBy 내에서 RequestContext.current()를 사용하여 "자신의 데이터만 수정 가능"과 같은 동적 권한 명세를 구현합니다.

---
