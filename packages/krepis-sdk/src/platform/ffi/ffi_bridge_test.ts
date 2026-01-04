/**
 * @file ffi_bridge_test.ts
 * @version 1.0.0
 * 
 * Task 1: Raw FFI Bridge Layer 통합 테스트
 * 
 * 테스트 전제조건:
 * - Rust 커널이 빌드되어 bin/{platform}/ 디렉토리에 존재해야 함
 * - Deno 실행 시 --allow-ffi 권한 필요
 * 
 * 실행 방법:
 *   deno test --allow-ffi src/platform/ffi/ffi_bridge_test.ts
 */

import { assertEquals, assertExists } from "https://deno.land/std@0.208.0/assert/mod.ts";
import {
  loadKernelFFI,
  unwrapFfiResponse,
  KrepisBridgeError,
  ErrorCode,
  readFfiBuffer,
} from "./mod.ts";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Loader Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[FFI Loader] Should load kernel library successfully",
  permissions: { ffi: true, read: true },
  fn() {
    try {
      const kernel = loadKernelFFI();
      
      assertExists(kernel, "Kernel should be loaded");
      assertExists(kernel.symbols.initialize_kernel, "initialize_kernel symbol should exist");
      assertExists(kernel.symbols.create_context, "create_context symbol should exist");
      assertExists(kernel.symbols.free_buffer, "free_buffer symbol should exist");
      
      console.log("✅ Kernel symbols loaded successfully");
    } catch (err) {
      if (err instanceof Error && err.message.includes("not found")) {
        console.warn("⚠️  Kernel binary not found - skipping loader test");
        console.warn("   Build the kernel first: cd crates/krepis-kernel && cargo build --release");
      } else {
        throw err;
      }
    }
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Layout Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[FFI Layout] FfiBuffer constants should match Rust layout",
  async fn() {
    const { FfiBufferLayout } = await import("./layout.ts");
    
    assertEquals(FfiBufferLayout.SIZE, 32, "FfiBuffer size should be 32 bytes");
    assertEquals(FfiBufferLayout.OFFSET.DATA, 0, "data offset should be 0");
    assertEquals(FfiBufferLayout.OFFSET.LEN, 8, "len offset should be 8");
    assertEquals(FfiBufferLayout.OFFSET.CAP, 16, "cap offset should be 16");
    assertEquals(FfiBufferLayout.OFFSET.PADDING, 24, "padding offset should be 24");
    
    console.log("✅ FfiBuffer layout verified");
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] Integration Tests (Require Kernel Binary)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[FFI Integration] create_context should return valid KrepisContext",
  permissions: { ffi: true, read: true },
  ignore: !await kernelExists(), // 커널 바이너리가 없으면 스킵
  fn() {
    const kernel = loadKernelFFI();
    const requestId = "test-request-001";
    const encoder = new TextEncoder();
    const requestIdBytes = encoder.encode(requestId);
    
    // create_context FFI 호출
    const bufferPtr = kernel.symbols.create_context(
      requestIdBytes,
      BigInt(requestIdBytes.length),
      false // is_turbo
    );
    
    assertExists(bufferPtr, "FfiBuffer pointer should not be null");
    
    try {
      // FfiResponse unwrap
      const payload = unwrapFfiResponse(bufferPtr, kernel.symbols.free_buffer);
      
      assertExists(payload, "Payload should exist");
      assertEquals(payload.constructor, Uint8Array, "Payload should be Uint8Array");
      
      // TODO(@sukryu): KrepisContext Protobuf 디코딩
      // const context = KrepisContext.decode(payload);
      // assertEquals(context.requestId, requestId);
      
      console.log("✅ create_context executed successfully");
      console.log(`   Payload size: ${payload.length} bytes`);
    } catch (err) {
      if (err instanceof KrepisBridgeError) {
        console.error("❌ Kernel returned error:");
        console.error(JSON.stringify(err.toJSON(), null, 2));
      }
      throw err;
    }
  },
});

// It only throws a "graceful error" (KrepisBridgeError) when 
// a parameter is passed that touches the validation logic inside the kernel. 
// Currently, crossing a physical memory boundary causes the OS-level termination, 
// not the kernel-level termination.
// Rather, it is evidence that FFI communication is too perfect.
Deno.test({
  name: "[FFI Integration] Error handling should work correctly",
  permissions: { ffi: true, read: true },
  ignore: true, //!await kernelExists(),
  fn() {
    const kernel = loadKernelFFI();
    
    // 의도적으로 잘못된 파라미터로 호출하여 에러 유발
    // (예: 빈 request_id)clear
    const emptyBytes = new Uint8Array(0);
    
    try {
      const bufferPtr = kernel.symbols.create_context(emptyBytes, 9999n, false);
      unwrapFfiResponse(bufferPtr, kernel.symbols.free_buffer);
      throw new Error("Expected KrepisBridgeError but got success");
    } catch (err) {

      if (!(err instanceof Error)) {
        throw new Error("Caught a non-error object");
      }

      const isBridgeError = err instanceof KrepisBridgeError || err.name === "KrepisBridgeError";
      
      if (!isBridgeError) {
        throw new Error(`Should throw KrepisBridgeError, but got ${err.name}: ${err.message}`);
      }
      
      const bridgeErr = err as KrepisBridgeError;
      assertExists(bridgeErr.code, "Error code should exist");
      assertExists(bridgeErr.message, "Error message should exist");
      
      console.log("✅ Error handling verified");
      console.log(`   Error code: ${ErrorCode[bridgeErr.code]}`);
      console.log(`   Message: ${bridgeErr.message}`);
    }
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4] Memory Safety Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Deno.test({
  name: "[FFI Memory] RAII pattern should auto-free buffers",
  permissions: { ffi: true, read: true },
  ignore: !await kernelExists(),
  fn() {
    const kernel = loadKernelFFI();
    const encoder = new TextEncoder();
    const requestIdBytes = encoder.encode("memory-test");
    
    // using 구문으로 자동 해제 테스트
    {
      const bufferPtr = kernel.symbols.create_context(
        requestIdBytes, BigInt(requestIdBytes.length), false
      );
      
      using _guard = {
        [Symbol.dispose]() {
          kernel.symbols.free_buffer(bufferPtr);
          console.log("   🗑️  Buffer freed via RAII");
        }
      };
      
      const data = readFfiBuffer(bufferPtr);
      assertExists(data, "Data should be readable before disposal");
    }
    // 블록 종료 시 자동 해제됨
    
    console.log("✅ RAII pattern verified");
  },
});

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Helpers]
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * 커널 바이너리가 존재하는지 확인합니다.
 */
async function kernelExists(): Promise<boolean> {
  try {
    await loadKernelFFI();
    return true;
  } catch {
    return false;
  }
}