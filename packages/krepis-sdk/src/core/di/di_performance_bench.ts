import { ServiceCollection } from "./SovereignContainer.ts";
import { ContextFactory } from "../context/ContextFactory.ts";

/**
 * Krepis DI Container Performance Stress Test
 * 1. Singleton Resolve: 앱 생명주기 동안 1번만 생성되는 서비스의 접근 속도
 * 2. Scoped Resolve: 매 요청(Context)마다 생성되는 서비스의 오버헤드
 * 3. Dependency Tree: 깊은 의존성 그래프(A->B->C) 해결 성능
 */

// [1] 테스트용 서비스 정의
class DatabaseService { name = "DB"; }
class Repository { constructor(public db: DatabaseService) {} }
class AuthService { constructor(public repo: Repository) {} }

const services = new ServiceCollection();

services.addSingleton(DatabaseService, () => new DatabaseService());
services.addScoped(Repository, (c) => new Repository(c.get(DatabaseService)));
services.addScoped(AuthService, (c) => new AuthService(c.get(Repository)));

const provider = services.build();
const mockOptions = { tenantId: "perf-test" };

// [2] 벤치마크 설계
Deno.bench({
  name: "DI: Singleton Resolve (Constant Time)",
  group: "di_resolve",
  baseline: true,
  fn() {
    // 이미 생성된 인스턴스를 가져오는 속도
    const db = provider.getSingleton(DatabaseService);
    void db.name;
  },
});

Deno.bench({
  name: "DI: Scoped Resolve (New Context/Burst)",
  group: "di_resolve",
  fn() {
    // 1. 컨텍스트 생성
    using ctx = ContextFactory.createSync(mockOptions);
    // 2. 스코프 생성
    const scope = provider.createScope(ctx);
    // 3. 의존성 트리 해결 (AuthService -> Repository -> DatabaseService)
    const auth = scope.get(AuthService);
    void auth.repo.db.name;
  },
});

Deno.bench({
  name: "DI: Scoped Resolve (Warm Scope)",
  group: "di_resolve",
  fn() {
    using ctx = ContextFactory.createSync(mockOptions);
    const scope = provider.createScope(ctx);
    
    // 한 스코프 내에서 100번 반복 호출 (캐싱 효율 확인)
    for (let i = 0; i < 100; i++) {
      const auth = scope.get(AuthService);
      void auth.repo.db.name;
    }
  },
});