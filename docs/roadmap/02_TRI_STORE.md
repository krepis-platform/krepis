# Tri-Store Architecture: 확률이 아닌 확정

**Status:** Future (Phase 5)  
**Phase:** 5 (AI 군단 운영)  
**Last Updated:** 2026-01-19  
**Prerequisites:** Phase 1-4 완료  

---

## TL;DR

**현재 AI 코딩 도구의 문제:**  
모든 것을 벡터 검색으로 해결 → 느리고 부정확

**Krepis Tri-Store 해결책:**  
O(1) Index + O(1) Graph + O(log N) Vector → 빠르고 정확

**결과:**  
1000배 빠른 조회, 100% 정확도 (심볼 검색)

---

## Context: 왜 Tri-Store가 필요한가?

### 현재 AI 코딩 시스템의 문제

대부분의 AI 코딩 도구 (Copilot, Cursor, Devin)는 다음과 같이 작동합니다:

```
User: "AuthService를 찾아줘"
  ↓
Embedding: "AuthService" → [0.23, 0.87, ..., 0.45]
  ↓
Vector Search: Cosine similarity 계산 (전체 코드베이스)
  ↓
Results: 
  1. UserAuthenticationService (0.92 similarity)
  2. AuthorizationService (0.89 similarity)
  3. AuthService (0.87 similarity) ← 3번째!
  ↓
Time: 500ms
```

**문제점:**
1. **느림:** 벡터 검색은 수백 밀리초 소요
2. **부정확:** 원하는 결과가 3번째에 나타날 수 있음
3. **혼동:** "AuthService"와 "UserAuthService" 구분 못함
4. **비효율:** 명확한 심볼 검색에 벡터 사용

### Tri-Store의 철학

> "확률(Vector)에 의존하지 말고, 확정(Index)으로 접근하라"

- **정확히 알고 있는 것:** Index/Graph로 O(1) 조회
- **의미론적 유사성:** Vector로 O(log N) 검색

---

## Solution: 3단계 저장소 전략

```
┌─────────────────────────────────────────────────────┐
│              User Query                             │
└─────────────────────────────────────────────────────┘
                      ↓
         Query Classifier (어떤 Store?)
                      ↓
    ┌─────────┬───────────────┬──────────┐
    ↓         ↓               ↓          
  Tier 1    Tier 2          Tier 3
  Index     Graph           Vector
  O(1)      O(1)            O(log N)
```

### Tier 1: Index Store (Sled)

**역할:** 심볼 테이블 (Symbol Table)

**용도:**
- Class/Function/Module 이름으로 직접 조회
- "AuthService는 어디?"
- "User 타입 정의는?"

**기술:** Sled (Embedded Key-Value DB)

**예시:**
```rust
// 저장
index_store.insert(
    tenant_id,
    "AuthService",
    FileLocation { id: 55, path: "src/services/auth.ts" }
);

// 조회 (O(1))
let loc = index_store.get(tenant_id, "AuthService");
// → FileLocation { id: 55, path: "src/services/auth.ts" }
// Time: ~10 microseconds
```

**데이터 구조:**
```
Key: "tenant_id::symbol_name"
Value: { id: u64, path: String, line: usize }

Example:
"tenant_A::AuthService" → { id: 55, path: "src/services/auth.ts", line: 10 }
```

---

### Tier 2: Graph Store (SurrealDB)

**역할:** 의존성 그래프 (Dependency Graph)

**용도:**
- "AuthService가 사용하는 서비스는?"
- "User 타입을 사용하는 함수들?"
- "이 변경이 영향을 주는 코드는?"

**기술:** SurrealDB (Graph Database)

**예시:**
```sql
-- 저장 (Graph Relation)
RELATE service:55->uses->service:92;
RELATE service:55->uses->repository:12;

-- 조회 (O(1) pointer traversal)
SELECT ->uses->service FROM service:55;
// → [service:92, repository:12]
// Time: ~10 microseconds
```

**Graph Schema:**
```
Node Types:
- service (e.g., AuthService)
- repository (e.g., UserRepository)
- model (e.g., User)
- function (e.g., validateEmail)

Edge Types:
- uses (A uses B)
- extends (A extends B)
- implements (A implements B)
- calls (A calls B)
- depends_on (A depends on B)
```

---

### Tier 3: Vector Store (Qdrant)

**역할:** 의미론적 검색 (Semantic Search)

**용도:**
- "로그인 기능과 비슷한 코드"
- "이메일 검증 로직"
- "에러 핸들링 패턴"

**기술:** Qdrant (Vector Database)

**예시:**
```typescript
// 저장
vector_store.insert({
  id: 55,
  vector: embed("Handles user authentication..."),
  metadata: {
    type: "service",
    name: "AuthService",
    summary: "Handles user authentication including login and token management"
  }
});

// 조회 (O(log N) ANN search)
let results = vector_store.search(
  embed("login functionality"),
  top_k: 5
);
// → [AuthService, LoginController, SessionManager, ...]
// Time: ~50 milliseconds
```

---

## Architecture: Query Flow

### Example 1: Exact Symbol Lookup

```
User: "AuthService를 찾아줘"
  ↓
Query Classifier: "Exact symbol" → Tier 1
  ↓
Sled.get("tenant_A::AuthService")
  ↓
Result: { id: 55, path: "src/services/auth.ts" }
Time: 10μs (1000x faster than vector!)
```

### Example 2: Dependency Traversal

```
User: "AuthService가 뭘 사용하나?"
  ↓
Query Classifier: "Dependency" → Tier 1 + Tier 2
  ↓
Step 1: Sled.get("AuthService") → id: 55
Step 2: Graph.traverse(55, "uses")
  ↓
Result: [UserRepository, TokenService, EmailValidator]
Time: 20μs
```

### Example 3: Semantic Search

```
User: "로그인과 비슷한 기능 찾아줘"
  ↓
Query Classifier: "Semantic" → Tier 3
  ↓
Qdrant.search(embed("login"))
  ↓
Results: [
  AuthService (0.95),
  SessionManager (0.87),
  OAuthHandler (0.82)
]
Time: 50ms (still acceptable)
```

---

## Implementation: Phase-by-Phase

### Phase 3: Single Store (Sled만)

**목표:** 개념 증명

```rust
// crates/krepis-kernel/src/index_store.rs
pub struct IndexStore {
    db: sled::Db,
}

impl IndexStore {
    pub fn insert(&self, tenant: TenantId, key: &str, loc: FileLocation) {
        let full_key = format!("{}::{}", tenant, key);
        self.db.insert(full_key, bincode::serialize(&loc)?)?;
    }
    
    pub fn get(&self, tenant: TenantId, key: &str) -> Option<FileLocation> {
        let full_key = format!("{}::{}", tenant, key);
        self.db.get(full_key)?
            .map(|bytes| bincode::deserialize(&bytes).unwrap())
    }
}
```

**성공 기준:**
- [ ] 10,000 symbols 조회 < 1ms
- [ ] Multi-tenant isolation 검증
- [ ] Crash recovery 테스트

---

### Phase 4: Add Graph (SurrealDB)

**목표:** 의존성 추적

```typescript
// Example: 코드 변경 시 영향 분석
const changed = "AuthService";

// Step 1: Get ID from Index
const id = await indexStore.get(tenantId, changed);

// Step 2: Find dependents from Graph
const dependents = await graphStore.query(`
  SELECT <-uses<-service 
  FROM service:${id}
`);

// Step 3: Alert developer
console.log(`${changed} 변경 시 영향받는 서비스:`, dependents);
```

**성공 기준:**
- [ ] 3-hop dependency 조회 < 10ms
- [ ] Cycle detection (circular dependencies)
- [ ] Graph 시각화 UI

---

### Phase 5: Add Vector (Qdrant)

**목표:** 의미론적 검색

```typescript
// Example: AI가 유사 코드 찾기
const userQuery = "이메일 검증 로직 필요해";

// Step 1: Embed query
const queryVector = await embed(userQuery);

// Step 2: Semantic search
const similar = await vectorStore.search({
  vector: queryVector,
  limit: 5,
  filter: { type: "function" }
});

// Step 3: Load actual code (Lazy loading)
const signatures = similar.map(r => 
  indexStore.getSignature(r.id)
);
```

**성공 기준:**
- [ ] Semantic search < 100ms
- [ ] Precision@5 > 90%
- [ ] No hallucination (Vector만 믿지 않음)

---

## Optimization: Signature-Based Lazy Loading

### 문제: Context Window 낭비

AI가 코드를 참조할 때 전체 구현을 로딩하면 토큰 낭비:

```typescript
// 전체 구현 (500 tokens)
class UserService {
  async createUser(email: string, password: string): Promise<User> {
    // Validation (50 lines)
    if (!this.isValidEmail(email)) throw new Error("Invalid email");
    if (password.length < 8) throw new Error("Password too short");
    
    // Hashing (20 lines)
    const hashedPassword = await bcrypt.hash(password, 10);
    
    // Database (30 lines)
    const user = await this.db.users.create({
      email,
      password: hashedPassword,
      createdAt: new Date()
    });
    
    // Events (20 lines)
    await this.eventBus.publish('user.created', user);
    
    return user;
  }
}
```

### 해결책: Caller vs Implementer Mode

**Caller Mode (AI가 호출만 할 때):**
```typescript
// Signature만 로딩 (50 tokens, 90% 절약!)
class UserService {
  /** @ai-summary Creates a new user account with validation */
  createUser(email: string, password: string): Promise<User>;
}
```

**Implementer Mode (AI가 수정할 때):**
```typescript
// Graph pointer 따라가서 전체 구현 로딩
const fullImpl = await graphStore.traverse(
  signatureId,
  "has_implementation"
);
```

### 데이터 구조

**Tier 1 (Index):**
```json
{
  "UserService::createUser": {
    "signature_id": 123,
    "impl_id": 456
  }
}
```

**Tier 2 (Graph):**
```
Node 123 (Signature)
  ├─ signature: "createUser(email: string, ...)"
  ├─ summary: "Creates a new user account"
  └─ has_implementation → Node 456

Node 456 (Implementation)
  └─ code: "async createUser(...) { ... }"
```

**AI Workflow:**
```typescript
// 1. AI needs to call function
const sig = indexStore.getSignature("UserService::createUser");
// → 50 tokens

// 2. AI needs to modify function  
const impl = graphStore.getImplementation(sig.impl_id);
// → 500 tokens (only when needed!)
```

---

## Synchronization: The Hard Problem

### Challenge: 3개 DB 동기화

```typescript
// Developer renames AuthService → UserAuthService
git mv src/services/AuthService.ts src/services/UserAuthService.ts
```

**필요한 업데이트:**
1. Tier 1 (Sled): Key 변경
2. Tier 2 (Graph): Node name 변경  
3. Tier 3 (Qdrant): Metadata 변경

**문제:** 2번과 3번 사이에 크래시하면 데이터 불일치!

### 해결책: Two-Phase Commit

```rust
fn rename_service(old: &str, new: &str) -> Result<()> {
    let txn = Transaction::begin();
    
    // Phase 1: Prepare (모든 DB에 변경 준비)
    txn.prepare_sled(old, new)?;
    txn.prepare_surreal(old, new)?;
    txn.prepare_qdrant(old, new)?;
    
    // Phase 2: Commit (원자적으로 전부 성공 or 전부 실패)
    txn.commit_all()?;
    
    Ok(())
}
```

**Phase 3-4에서는 하지 말 것:**
- Phase 3: Sled만 사용 (단일 DB, 동기화 불필요)
- Phase 4: Sled + Graph (2개, 간단한 2PC)
- Phase 5: 3개 전체 (복잡한 2PC)

---

## Multi-Tenant Isolation

### Tier 1 (Sled): Key Prefixing

```rust
// Tenant A
"tenant_A::AuthService" → { id: 55, ... }

// Tenant B
"tenant_B::AuthService" → { id: 123, ... }
```

**격리:** Key namespace로 완전 분리

---

### Tier 2 (SurrealDB): Namespace Isolation

```sql
-- Tenant A namespace
USE NS tenant_a;
RELATE service:55->uses->service:92;

-- Tenant B namespace  
USE NS tenant_b;
RELATE service:123->uses->service:456;
```

**격리:** Database namespace로 분리

---

### Tier 3 (Qdrant): Collection Partitioning

```rust
// Tenant A collection
qdrant.create_collection("tenant_a_vectors");

// Tenant B collection
qdrant.create_collection("tenant_b_vectors");
```

**격리:** Collection 레벨 분리

---

## Success Criteria (Phase 5)

**정량적:**
- [ ] Tier 1 조회 < 1ms (p99)
- [ ] Tier 2 3-hop < 10ms (p99)
- [ ] Tier 3 검색 < 100ms (p99)
- [ ] 10,000 symbols 동시 조회 가능
- [ ] Multi-tenant 격리 검증

**정성적:**
- [ ] Vector 의존도 < 10% (대부분 Index/Graph로 해결)
- [ ] AI가 "정확한 코드를 빠르게" 찾음
- [ ] "확률이 아닌 확정" 철학 증명

---

## Trade-offs

### 장점

1. **속도:** O(1) vs O(log N) = 1000x 빠름
2. **정확도:** 심볼 검색 100% 정확
3. **효율:** 토큰 90% 절약 (Lazy loading)

### 단점

1. **복잡도:** 3개 DB 동기화 어려움
2. **메모리:** 3개 DB = 3배 메모리
3. **운영:** 3개 DB 모니터링 필요

### 대안 고려

**PostgreSQL 1개로 모든 것 해결?**
```sql
-- Index (BTREE)
CREATE INDEX idx_symbols ON code_index(tenant_id, symbol);

-- Graph (Recursive CTE)
WITH RECURSIVE deps AS (...) SELECT ...;

-- Vector (pgvector extension)
SELECT * FROM embeddings ORDER BY vector <-> query_vector LIMIT 5;
```

**장점:** 단일 DB, 성숙한 기술  
**단점:** 각 영역에서 최적화되지 않음

**결정:** Phase 3-4는 PostgreSQL로 시작, Phase 5에 Tri-Store

---

## References

- Master Report (2026-01-17): 원본 아이디어
- Phase 5 Roadmap: `roadmap/phase5/OBJECTIVES.md`
- Shadow Tagging: `architecture/ai-native/SHADOW_TAGGING.md`
- V8 Integration: `architecture/neural-os/V8_ISOLATES.md`

---

**"확률에 의존하지 말고, 확정으로 접근하라"**

*Tier 1-2가 90% 해결, Tier 3는 정말 필요할 때만*