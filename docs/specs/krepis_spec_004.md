# **📑 \[Krepis-Spec-004\] Pure Domain Repository Specification (v1.1.0)**

**버전:** v1.1.0 (Concurrency & Load Strategy 확장)

**상태:** Final Draft

**모듈명:** @krepis/core/repository

---

## **Ⅰ. 설계 철학 (Design Philosophy)**

1. **Persistence Ignorance:** 도메인 모델은 자신이 어떻게 저장되는지(SQL, NoSQL 등)에 대해 완전히 무지해야 합니다.  
2. **Aggregate Integrity:** 리포지토리는 항상 유효한 상태의 애그리거트 루트(Aggregate Root)를 반환하며, 부분적인 데이터 로드로 인한 도메인 로직 오염을 방지합니다.  
3. **Optimistic Concurrency:** 동시 수정 문제를 방지하기 위해 버전 기반의 낙관적 잠금을 표준으로 채택합니다.  
4. **Specification-Driven:** 복잡한 검색 조건은 문자열이나 객체가 아닌 타입 안정성이 보장된 Specification 객체를 통해 전달됩니다.

---

## **Ⅱ. 핵심 인터페이스 정의**

### **1\. 표준 저장소 인터페이스 (The Generic Port)**

모든 도메인 저장소가 상속받을 기본 규격입니다.

TypeScript

export interface IRepository\<TEntity, TId\> {  
  findById(id: TId, options?: ILoadOptions): Promise\<TEntity | null\>;  
  save(entity: TEntity): Promise\<void\>;  
  delete(id: TId): Promise\<void\>;  
    
  /\*\* 명세 패턴을 통한 복합 쿼리 \*/  
  find(spec: ISpecification\<TEntity\>, options?: ILoadOptions): Promise\<TEntity\[\]\>;  
}

/\*\* 데이터 로드 전략: 연관 객체 포함 여부 결정 \*/  
export interface ILoadOptions {  
  readonly include?: string\[\]; // 도메인이 이해하는 관계 명칭  
}

### **2\. 엔티티 버전 관리 (Concurrency Guard)**

낙관적 잠금을 위해 도메인 엔티티는 다음 규격을 준수해야 합니다.

TypeScript

export interface IVersionable {  
  readonly version: number;  
}

---

## **Ⅲ. 현실적인 구현 전략 (Adapters)**

### **1\. Mapper 패턴 (Deep-Copy & Type-Safe)**

인프라 어댑터 내부에서만 작동하며, DB 레코드와 엔티티 간의 완벽한 격리를 제공합니다.

TypeScript

export class UserMapper {  
  static toDomain(record: PrismaUserRecord): User {  
    return new User({  
      id: record.id,  
      email: record.email,  
      version: record.version, // 버전 정보 포함  
      profile: record.profile ? ProfileMapper.toDomain(record.profile) : undefined  
    });  
  }

  static toPersistence(user: User): any {  
    return {  
      id: user.id,  
      email: user.email,  
      version: user.version,  
      // DB 스키마에 맞는 구조로 변환  
    };  
  }  
}

### **2\. Specification 변환기 (Query Abstraction)**

도메인의 의도를 인프라의 언어(SQL/Prisma)로 번역하는 역할을 수행합니다.

TypeScript

export class PrismaSpecConverter {  
  static toPrismaWhere\<T\>(spec: ISpecification\<T\>): any {  
    // 예: UserActiveSpec \-\> { status: 'ACTIVE' }  
    return spec.toQuery();  
  }  
}

---

## **Ⅳ. 방어적 저장 로직 (Optimistic Locking)**

인프라 어댑터의 save() 구현 시, 버전 체크를 강제하여 동시성 문제를 해결합니다.

TypeScript

// infrastructure/persistence/prisma/PrismaUserRepository.ts  
async save(user: User): Promise\<void\> {  
  const data \= UserMapper.toPersistence(user);  
    
  try {  
    await this.prisma.user.update({  
      where: {   
        id: user.id,  
        version: user.version // 현재 버전이 일치할 때만 업데이트  
      },  
      data: {  
        ...data,  
        version: { increment: 1 } // 성공 시 버전 업  
      }  
    });  
  } catch (err) {  
    if (err.code \=== 'P2025') { // Prisma Record Not Found (Version Mismatch)  
      throw new ConcurrencyException(\`User(${user.id}) was modified by another process.\`);  
    }  
    throw err;  
  }  
}

---

## **Ⅴ. 기대 효과 (KPI)**

1. **신뢰성(Reliability):** 동시 수정 시 에러를 즉시 감지하여 데이터 정합성 파괴 방지.  
2. **유연성(Flexibility):** DB를 PostgreSQL에서 MongoDB로 교체해도 도메인 로직 수정 0%.  
3. **가독성(Readability):** 리포지토리 메서드명이 비즈니스 언어(UBIQUITOUS LANGUAGE)와 완벽히 일치.

---
