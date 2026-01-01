import { assertEquals } from "jsr:@std/assert";
import {
  encodeInitRequest,
  decodeInitResponse,
  initializeKernel,
  type KnulConfigData,
} from "../mod.ts";
import { KrepisContext } from "../src/native/context.ts";
import { unloadKernel } from "../src/native/bindings.ts";

Deno.test({
  name: "FFI Integrated Test Suite",
  sanitizeResources: false,
  fn: async (t) => {

    await t.step("create native context", () => {
      const ctx = KrepisContext.create({ requestId: "test-req-001", isTurboMode: true });
      const buffer = ctx.toBuffer();
      assertEquals(buffer.length > 0, true);
    });

    await t.step("initialize kernel with protobuf", () => {
      const ctx = KrepisContext.create({
        requestId: "test-init-001",
        isTurboMode: false,
      });
      
      const config: KnulConfigData = {
        enable0rtt: true,
        compressionLevel: 9,
        maxStreams: 10000,
      };
      
      const request = encodeInitRequest(ctx, config);
      const response = initializeKernel(request);
      
      const decoded = decodeInitResponse(response);
      assertEquals(decoded.success, true);
      assertEquals(decoded.errorMessage, "");
    });

    await t.step("handle turbo mode context", () => {
      const standardCtx = KrepisContext.create({
        requestId: "standard-001",
        isTurboMode: false,
      });
      
      const turboCtx = KrepisContext.create({
        requestId: "turbo-001",
        isTurboMode: true,
      });
      
      assertEquals(standardCtx.toBuffer().length > 0, true);
      assertEquals(turboCtx.toBuffer().length > 0, true);
    });

    unloadKernel();
  },
});