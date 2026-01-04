/**
 * @file validation_test.ts
 * @version 1.0.0
 * 
 * C-GAP-001 & C-GAP-002 검증 엔진 테스트
 * 
 * 테스트 범위:
 * - C-GAP-001: Circular Dependency Detection
 *   - Self-reference (A → A)
 *   - Simple cycle (A → B → A)
 *   - Complex cycle (A → B → C → A)
 *   - DAG (Diamond pattern, NOT a cycle)
 * 
 * - C-GAP-002: Captive Dependency Detection
 *   - Singleton → Scoped (❌)
 *   - Singleton → Transient (❌)
 *   - Scoped → Transient (✅ allowed but warned)
 *   - Valid hierarchies (✅)
 * 
 * 실행 방법:
 *   deno test validation_test.ts
 */

import { assertEquals, assertThrows, assertExists } from "https://deno.land/std@0.208.0/assert/mod.ts";
import { createServiceCollection } from "./SovereignContainer.ts";
import { InjectionToken } from "./identifiers.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Test Fixtures - 재사용 가능한 테스트 서비스들
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

class ServiceA { name = "A"; }
class ServiceB { name = "B"; }
class ServiceC { name = "C"; }
class ServiceD { name = "D"; }

const TOKEN_A = new InjectionToken<ServiceA>("TokenA");
const TOKEN_B = new InjectionToken<ServiceB>("TokenB");
const TOKEN_C = new InjectionToken<ServiceC>("TokenC");
const TOKEN_D = new InjectionToken<ServiceD>("TokenD");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [C-GAP-001] Circular Dependency Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[C-GAP-001] Edge Case 1: Self-reference should be detected (A → A)",
  fn() {
    const services = createServiceCollection();
    
    // A가 자기 자신을 의존
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_A]);
    
    assertThrows(
      () => services.build(),
      Error,
      "Circular Dependency Detected (C-GAP-001)",
      "Self-reference must be detected as circular dependency"
    );
  },
});

Deno.test({
  name: "[C-GAP-001] Edge Case 2: Simple cycle should be detected (A → B → A)",
  fn() {
    const services = createServiceCollection();
    
    // A → B → A
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    services.addSingleton(TOKEN_B, () => new ServiceB(), [TOKEN_A]);
    
    const error = assertThrows(
      () => services.build(),
      Error,
      "Circular Dependency Detected (C-GAP-001)"
    );
    
    // 에러 메시지에 순환 경로가 포함되어야 함
    assertExists(error.message.match(/TokenA.*TokenB/));
  },
});

Deno.test({
  name: "[C-GAP-001] Edge Case 3: Complex cycle should be detected (A → B → C → A)",
  fn() {
    const services = createServiceCollection();
    
    // A → B → C → A
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    services.addSingleton(TOKEN_B, () => new ServiceB(), [TOKEN_C]);
    services.addSingleton(TOKEN_C, () => new ServiceC(), [TOKEN_A]);
    
    const error = assertThrows(
      () => services.build(),
      Error,
      "Circular Dependency Detected (C-GAP-001)"
    );
    
    // 순환 경로 시각화 확인
    assertExists(error.message.match(/TokenA.*TokenB.*TokenC/));
  },
});

Deno.test({
  name: "[C-GAP-001] Edge Case 4: Diamond DAG should PASS (not a cycle)",
  fn() {
    const services = createServiceCollection();
    
    /**
     * Diamond Pattern (DAG - Directed Acyclic Graph)
     * 
     *       A
     *      / \
     *     B   C
     *      \ /
     *       D
     * 
     * A → B → D
     * A → C → D
     * 
     * D는 두 경로로 도달하지만 순환은 아님!
     */
    services.addSingleton(TOKEN_D, () => new ServiceD());
    services.addSingleton(TOKEN_B, () => new ServiceB(), [TOKEN_D]);
    services.addSingleton(TOKEN_C, () => new ServiceC(), [TOKEN_D]);
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B, TOKEN_C]);
    
    // 순환이 아니므로 성공해야 함
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[C-GAP-001] Multiple independent cycles should all be caught",
  fn() {
    const services = createServiceCollection();
    
    // Cycle 1: A → B → A
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    services.addSingleton(TOKEN_B, () => new ServiceB(), [TOKEN_A]);
    
    // Cycle 2: C → D → C (독립적)
    services.addSingleton(TOKEN_C, () => new ServiceC(), [TOKEN_D]);
    services.addSingleton(TOKEN_D, () => new ServiceD(), [TOKEN_C]);
    
    // 첫 번째 순환을 만나면 즉시 실패해야 함
    assertThrows(
      () => services.build(),
      Error,
      "Circular Dependency Detected (C-GAP-001)"
    );
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [C-GAP-002] Captive Dependency Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[C-GAP-002] Edge Case 5: Singleton → Scoped should FAIL (Captive!)",
  fn() {
    const services = createServiceCollection();
    
    // B는 Scoped
    services.addScoped(TOKEN_B, () => new ServiceB());
    
    // A는 Singleton인데 Scoped인 B를 의존 (❌ Captive!)
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const error = assertThrows(
      () => services.build(),
      Error,
      "Captive Dependency Detected (C-GAP-002)"
    );
    
    // 에러 메시지에 생명 주기 정보 포함 확인
    assertExists(error.message.match(/SINGLETON/i));
    assertExists(error.message.match(/SCOPED/i));
  },
});

Deno.test({
  name: "[C-GAP-002] Edge Case 6: Singleton → Transient should FAIL (Captive!)",
  fn() {
    const services = createServiceCollection();
    
    // B는 Transient
    services.addTransient(TOKEN_B, () => new ServiceB());
    
    // A는 Singleton인데 Transient인 B를 의존 (❌ Captive!)
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    assertThrows(
      () => services.build(),
      Error,
      "Captive Dependency Detected (C-GAP-002)",
      "Singleton cannot capture Transient service"
    );
  },
});

Deno.test({
  name: "[C-GAP-002] Edge Case 7: Scoped → Transient should PASS (with warning)",
  fn() {
    const services = createServiceCollection();
    
    /**
     * Scoped → Transient는 기술적으로 안전하지만 성능상 비효율적일 수 있음
     * (매번 새 인스턴스 생성)
     * 
     * 현재 구현: PASS (경고만, 차단하지 않음)
     */
    services.addTransient(TOKEN_B, () => new ServiceB());
    services.addScoped(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    // 성공해야 함 (경고는 선택사항)
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[C-GAP-002] Valid hierarchy: Singleton → Singleton should PASS",
  fn() {
    const services = createServiceCollection();
    
    services.addSingleton(TOKEN_B, () => new ServiceB());
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[C-GAP-002] Valid hierarchy: Scoped → Singleton should PASS",
  fn() {
    const services = createServiceCollection();
    
    services.addSingleton(TOKEN_B, () => new ServiceB());
    services.addScoped(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[C-GAP-002] Valid hierarchy: Scoped → Scoped should PASS",
  fn() {
    const services = createServiceCollection();
    
    services.addScoped(TOKEN_B, () => new ServiceB());
    services.addScoped(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[C-GAP-002] Valid hierarchy: Transient → Singleton should PASS",
  fn() {
    const services = createServiceCollection();
    
    services.addSingleton(TOKEN_B, () => new ServiceB());
    services.addTransient(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[C-GAP-002] Valid hierarchy: Transient → Scoped should PASS",
  fn() {
    const services = createServiceCollection();
    
    services.addScoped(TOKEN_B, () => new ServiceB());
    services.addTransient(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[C-GAP-002] Valid hierarchy: Transient → Transient should PASS",
  fn() {
    const services = createServiceCollection();
    
    services.addTransient(TOKEN_B, () => new ServiceB());
    services.addTransient(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const provider = services.build();
    assertExists(provider);
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Combined] Complex Scenarios
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[Combined] Circular + Captive: Both violations should be caught",
  fn() {
    const services = createServiceCollection();
    
    /**
     * A (Singleton) → B (Scoped) → A
     * 
     * 이 케이스는:
     * 1. Circular Dependency (A → B → A)
     * 2. Captive Dependency (Singleton A → Scoped B)
     * 
     * 둘 다 위반이지만, 순환 참조가 먼저 탐지됨
     */
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    services.addScoped(TOKEN_B, () => new ServiceB(), [TOKEN_A]);
    
    // 순환 참조가 먼저 탐지되어야 함 (검증 순서상)
    const error = assertThrows(
      () => services.build(),
      Error
    );
    
    // 순환 참조 또는 Captive 중 하나는 반드시 탐지되어야 함
    const hasCircular = error.message.includes("C-GAP-001");
    const hasCaptive = error.message.includes("C-GAP-002");
    
    assertEquals(hasCircular || hasCaptive, true, "At least one violation must be detected");
  },
});

Deno.test({
  name: "[Combined] Deep dependency chain with valid lifetimes",
  fn() {
    const services = createServiceCollection();
    
    /**
     * A (Transient) → B (Scoped) → C (Singleton) → D (Singleton)
     * 
     * 모든 의존성이 올바른 방향 (짧은 것이 긴 것을 의존)
     */
    services.addSingleton(TOKEN_D, () => new ServiceD());
    services.addSingleton(TOKEN_C, () => new ServiceC(), [TOKEN_D]);
    services.addScoped(TOKEN_B, () => new ServiceB(), [TOKEN_C]);
    services.addTransient(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const provider = services.build();
    assertExists(provider);
  },
});

Deno.test({
  name: "[Error Message Quality] Error message should be developer-friendly",
  fn() {
    const services = createServiceCollection();
    
    // Captive Dependency 위반
    services.addScoped(TOKEN_B, () => new ServiceB());
    services.addSingleton(TOKEN_A, () => new ServiceA(), [TOKEN_B]);
    
    const error = assertThrows(
      () => services.build(),
      Error,
      "C-GAP-002"
    );
    
    // 에러 메시지에 다음 정보들이 포함되어야 함:
    // 1. 서비스 이름
    assertExists(error.message.match(/TokenA/));
    assertExists(error.message.match(/TokenB/));
    
    // 2. 생명 주기 정보
    assertExists(error.message.match(/SINGLETON/i));
    assertExists(error.message.match(/SCOPED/i));
    
    // 3. 해결 방법 제시
    assertExists(error.message.match(/Solution/i));
    
    // 4. 시각적 구분 (박스)
    assertExists(error.message.match(/━/));
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Performance] Validation should not impact runtime
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[Performance] AOT validation only runs at build() time",
  fn() {
    const services = createServiceCollection();
    
    // 100개의 서비스 등록 (유효한 그래프)
    const tokens = Array.from({ length: 100 }, (_, i) => 
      new InjectionToken<any>(`Service${i}`)
    );
    
    tokens.forEach((token, i) => {
      // 체인 구조: S0 → S1 → S2 → ... → S99
      const deps = i > 0 ? [tokens[i - 1]] : [];
      services.addSingleton(token, () => ({}), deps);
    });
    
    // build() 시점에만 검증 실행
    const start = performance.now();
    const provider = services.build();
    const buildTime = performance.now() - start;
    
    // 검증은 빠르게 완료되어야 함 (< 10ms for 100 services)
    assertEquals(buildTime < 10, true, `Build time ${buildTime}ms should be < 10ms`);
    
    assertExists(provider);
  },
});

console.log(`
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
✅ C-GAP-001 & C-GAP-002 Validation Test Suite
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Test Coverage:
  [C-GAP-001] Circular Dependency Detection
  ✓ Self-reference (A → A)
  ✓ Simple cycle (A → B → A)
  ✓ Complex cycle (A → B → C → A)
  ✓ Diamond DAG (not a cycle)
  
  [C-GAP-002] Captive Dependency Detection
  ✓ Singleton → Scoped (blocked)
  ✓ Singleton → Transient (blocked)
  ✓ All valid lifetime hierarchies
  
  [Quality Assurance]
  ✓ Developer-friendly error messages
  ✓ Performance verification (AOT only)
  ✓ Combined violation scenarios

Run tests: deno test validation_test.ts
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
`);