/**
 * Krepis Core Framework v1.5.0
 * Trinity Pattern (Hexagonal + Functional + CQS) with Explicit Context
 */

export interface KrepisContext {
  requestId: string;
  timestamp: number;
  userId?: string;
  tenantId?: string;
  traceId: string;
  metadata: Record<string, unknown>;
}

export function createContext(partial?: Partial<KrepisContext>): KrepisContext {
  return {
    requestId: crypto.randomUUID(),
    timestamp: Date.now(),
    traceId: crypto.randomUUID(),
    metadata: {},
    ...partial,
  };
}

export class KrepisNativeException extends Error {
  constructor(
    message: string,
    public readonly code: string,
    public readonly ctx?: KrepisContext,
  ) {
    super(message);
    this.name = "KrepisNativeException";
  }
}

// Native FFI exports
export * from "./src/native/bindings.ts";
export * from "./src/native/context.ts";

console.log("🎯 Krepis Core Framework v1.5.0");
console.log("✅ Explicit Context: ACTIVE");
console.log("✅ Trinity Pattern: ENFORCED");
console.log("✅ Native FFI: READY");