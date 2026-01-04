/**
 * @file core_test.ts
 * @version 1.0.0
 * 
 * Task 2: Sovereign Context & DI Layer 통합 테스트
 * 
 * 테스트 범위:
 * - Context 생성 및 Protobuf 디코딩
 * - Disposable 패턴 (using)
 * - DI Container (Scoped, Singleton, Transient)
 * - Context와 DI 통합
 * 
 * 실행 방법:
 *   deno test --allow-ffi --allow-read src/core/core_test.ts
 */

import { assertEquals, assertExists, assertThrows } from "https://deno.land/std@0.208.0/assert/mod.ts";
import {
  type IKrepisContext,
  ContextFactory,
  ContextValidator,
  isKrepisContext,
  isDisposed,
} from "./context/mod.ts";
import {
  createServiceCollection,
  InjectionToken,
  KREPIS_CONTEXT,
} from "./di/mod.ts";
import { Constructor } from "./di/identifiers.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Context Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[Context] ContextValidator should validate options correctly",
  fn() {
    // Valid options
    const validResult = ContextValidator.validate({
      tenantId: "test-tenant",
    });
    assertEquals(validResult.isValid, true);
    
    // Invalid options (missing tenantId)
    const invalidResult = ContextValidator.validate({
      tenantId: "",
    });
    assertEquals(invalidResult.isValid, false);
    assertExists(invalidResult.errors);
    
    // Priority out of range
    const invalidPriority = ContextValidator.validate({
      tenantId: "test",
      priority: 15, // max is 10
    });
    assertEquals(invalidPriority.isValid, false);
  },
});

Deno.test({
  name: "[Context] ContextFactory should create valid context",
  permissions: { ffi: true, read: true },
  ignore: !await kernelExists(),
  async fn() {
    using ctx = await ContextFactory.create({
      tenantId: "test-tenant",
      isTurboMode: false,
      metadata: { key: "value" },
    });
    
    assertExists(ctx);
    assertEquals(isKrepisContext(ctx), true);
    assertEquals(ctx.tenantId, "test-tenant");
    assertEquals(ctx.isTurboMode, false);
    assertExists(ctx.requestId);
    assertExists(ctx.traceId);
    
    // Metadata access
    assertEquals(ctx.getMetadata("key"), "value");
    assertEquals(ctx.getMetadata("nonexistent"), undefined);
    
    console.log(`✅ Context created: ${ctx.requestId}`);
  },
});

Deno.test({
  name: "[Context] Disposable pattern should work correctly",
  permissions: { ffi: true, read: true },
  ignore: !await kernelExists(),
  async fn() {
    let ctx: IKrepisContext;
    
    {
      using _ctx = await ContextFactory.create({ tenantId: "disposable-test" });
      ctx = _ctx;
      
      // Inside scope - should be active
      assertEquals(isDisposed(ctx), false);
      assertEquals(ctx.requestId, _ctx.requestId);
    }
    // Outside scope - should be disposed
    
    // Accessing disposed context should throw
    assertThrows(
      () => ctx.requestId,
      Error,
      "disposed"
    );
    
    console.log("✅ Disposable pattern verified");
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] DI Container Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Test Services
const COUNTER = new InjectionToken<Counter>("Counter");
const MESSAGE_SERVICE = new InjectionToken<MessageService>("MessageService");

class Counter {
  private count = 0;
  
  increment(): number {
    return ++this.count;
  }
  
  getValue(): number {
    return this.count;
  }
}

class MessageService {
  constructor(private readonly ctx: IKrepisContext) {}
  
  getMessage(): string {
    return `Hello from ${this.ctx.tenantId}`;
  }
}

Deno.test({
  name: "[DI] ServiceCollection should build provider correctly",
  fn() {
    const services = createServiceCollection();
    
    services.addSingleton(COUNTER, Counter);
    services.addScoped(MESSAGE_SERVICE, MessageService as Constructor<MessageService>, [KREPIS_CONTEXT]);
    
    const provider = services.build();
    
    assertExists(provider);
    assertEquals(provider.has(COUNTER), true);
    assertEquals(provider.has(MESSAGE_SERVICE), true);
    
    console.log("✅ ServiceProvider built successfully");
  },
});

Deno.test({
  name: "[DI] Singleton lifetime should return same instance",
  fn() {
    const services = createServiceCollection();
    services.addSingleton(COUNTER, Counter);
    
    const provider = services.build();
    
    const instance1 = provider.getSingleton(COUNTER);
    const instance2 = provider.getSingleton(COUNTER);
    
    assertEquals(instance1, instance2, "Singleton should return same instance");
    
    instance1.increment();
    assertEquals(instance2.getValue(), 1, "State should be shared");
    
    console.log("✅ Singleton lifetime verified");
  },
});

Deno.test({
  name: "[DI] Scoped lifetime should be context-bound",
  permissions: { ffi: true, read: true },
  ignore: !await kernelExists(),
  async fn() {
    const services = createServiceCollection();
    services.addScoped(MESSAGE_SERVICE, MessageService as Constructor<MessageService>, [KREPIS_CONTEXT]);
    services.addScoped(COUNTER, Counter);
    
    const provider = services.build();
    
    using ctx = await ContextFactory.create({ tenantId: "scoped-test" });
    using scope = provider.createScope(ctx);
    
    const msg1 = scope.get(MESSAGE_SERVICE);
    const msg2 = scope.get(MESSAGE_SERVICE);
    
    assertEquals(msg1, msg2, "Scoped should return same instance within scope");
    assertEquals(msg1.getMessage(), "Hello from scoped-test");
    
    // Counter should also be scoped
    const counter1 = scope.get(COUNTER);
    counter1.increment();
    const counter2 = scope.get(COUNTER);
    assertEquals(counter2.getValue(), 1, "Scoped state should be preserved");
    
    console.log("✅ Scoped lifetime verified");
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Context + DI Integration Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[Integration] Context should be automatically injected into scoped services",
  permissions: { ffi: true, read: true },
  ignore: !await kernelExists(),
  async fn() {
    const services = createServiceCollection();
    services.addScoped(MESSAGE_SERVICE, MessageService as Constructor<MessageService>, [KREPIS_CONTEXT]);
    
    const provider = services.build();
    
    using ctx = await ContextFactory.create({
      tenantId: "integration-test",
      metadata: { source: "test" },
    });
    
    using scope = provider.createScope(ctx);
    
    // KREPIS_CONTEXT should be automatically available
    const injectedCtx = scope.get(KREPIS_CONTEXT);
    assertEquals(injectedCtx.requestId, ctx.requestId);
    assertEquals(injectedCtx.tenantId, "integration-test");
    
    // MessageService should receive context
    const messageService = scope.get(MESSAGE_SERVICE);
    assertEquals(messageService.getMessage(), "Hello from integration-test");
    
    console.log("✅ Context injection verified");
  },
});

Deno.test({
  name: "[Integration] Scoped container disposal should not affect context",
  permissions: { ffi: true, read: true },
  ignore: !await kernelExists(),
  async fn() {
    const services = createServiceCollection();
    services.addScoped(COUNTER, Counter);
    
    const provider = services.build();
    
    using ctx = await ContextFactory.create({ tenantId: "disposal-test" });
    
    // First scope
    {
      using scope = provider.createScope(ctx);
      const counter = scope.get(COUNTER);
      counter.increment();
      assertEquals(counter.getValue(), 1);
    }
    // Scope disposed, but context should still be active
    
    // Context should still be accessible
    assertEquals(ctx.tenantId, "disposal-test");
    assertExists(ctx.requestId);
    
    // Second scope - should get new counter instance
    {
      using scope = provider.createScope(ctx);
      const counter = scope.get(COUNTER);
      assertEquals(counter.getValue(), 0, "New scope should get fresh instance");
    }
    
    console.log("✅ Scope disposal behavior verified");
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Helpers]
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

async function kernelExists(): Promise<boolean> {
  try {
    const { loadKernelFFI } = await import("../platform/ffi/loader.ts");
    loadKernelFFI();
    return true;
  } catch {
    return false;
  }
}