/**
 * @file SovereignContext.ts
 * @version 1.0.0
 * @spec [Spec-001] Context Propagation v1.2.0
 * @spec [Spec-Dev-001] Memory Safety v1.6.0
 * 
 * Krepis Sovereign Context의 구현체.
 * 커널로부터 받은 Protobuf 바이너리를 래핑하고 RAII 패턴으로 생명주기를 관리합니다.
 */

import * as protobuf from "npm:protobufjs@^7.2.5";
import {
  type IKrepisContext,
  type ContextOptions,
  ContextState,
} from "./IKrepisContext.ts";

const Root = protobuf.Root || (protobuf as any).default?.Root;
if (!Root) {
  throw new Error("[FFI Envelope] Failed to load protobuf.Root. Check protobufjs installation.");
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [1] Protobuf Schema Definition
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * KrepisContext Protobuf 스키마.
 * 
 * 참조: proto/context.proto
 */
const root = Root.fromJSON({
  nested: {
    krepis: {
      nested: {
        core: {
          nested: {
            KrepisContext: {
              fields: {
                request_id: { type: "string", id: 1 },
                tenant_id: { type: "string", id: 2 },
                priority: { type: "uint32", id: 3 },
                is_turbo_mode: { type: "bool", id: 4 },
                trace_id: { type: "string", id: 5 },     
                timestamp: { type: "int64", id: 6 },
                metadata: { 
                  keyType: "string", 
                  type: "string", 
                  id: 7 
                } as protobuf.IMapField,
              },
            },
          },
        },
      },
    },
  },
});

const KrepisContextProto = root.lookupType("krepis.core.KrepisContext");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [2] Protobuf Data Interface
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Protobuf 디코딩 결과 타입.
 */
interface KrepisContextData {
  requestId: string;
  tenantId: string;
  priority: number;
  isTurboMode: boolean;
  traceId: string;
  timestamp: number | Long;
  metadata: { [key: string]: string };
}

// Long 타입 지원 (protobufjs)
interface Long {
  low: number;
  high: number;
  unsigned: boolean;
  toNumber(): number;
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [3] SovereignContext Implementation
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * Krepis Sovereign Context 구현체.
 * 
 * 이 클래스는 Rust 커널로부터 받은 Protobuf 바이너리를 파싱하고,
 * TS에서 사용 가능한 형태로 제공합니다.
 * 
 * ⚠️ 직접 생성하지 마십시오. ContextFactory.create()를 사용하십시오.
 */
export class SovereignContext implements IKrepisContext {
  // ─────────────────────────────────────────────────────────────────────────────
  // Private Fields
  // ─────────────────────────────────────────────────────────────────────────────
  
  private readonly _binary: Uint8Array;
  private readonly _data: KrepisContextData;
  private _state: ContextState;
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Constructor (Internal)
  // ─────────────────────────────────────────────────────────────────────────────
  
  /**
   * @internal
   * ContextFactory에서만 호출됩니다.
   */
  constructor(binary: Uint8Array) {
    this._binary = binary;
    try {
      const message = KrepisContextProto.decode(binary);
      // toObject를 통해 명확한 객체로 변환
      const decoded = KrepisContextProto.toObject(message, {
        defaults: true,
        longs: String,
      }) as any;

      this._data = {
        requestId: decoded.requestId || decoded.request_id,
        tenantId: decoded.tenantId || decoded.tenant_id,
        priority: Number(decoded.priority),
        isTurboMode: Boolean(decoded.isTurboMode ?? decoded.is_turbo_mode),
        traceId: decoded.traceId || decoded.trace_id,
        timestamp: Number(decoded.timestamp),
        metadata: decoded.metadata || {},
      };
      this._state = ContextState.Active;
    } catch (err) {
      this._state = ContextState.Faulted;
      throw new Error(
        `[SovereignContext] Failed to decode Protobuf: ${
          err instanceof Error ? err.message : String(err)
        }`
      );
    }
  }
  
  // ─────────────────────────────────────────────────────────────────────────────
  // IKrepisContext Implementation
  // ─────────────────────────────────────────────────────────────────────────────
  
  get requestId(): string {
    this.ensureActive();
    return this._data.requestId;
  }
  
  get tenantId(): string {
    this.ensureActive();
    return this._data.tenantId;
  }
  
  get traceId(): string {
    this.ensureActive();
    return this._data.traceId;
  }
  
  get isTurboMode(): boolean {
    this.ensureActive();
    return this._data.isTurboMode;
  }
  
  get timestamp(): bigint {
    this.ensureActive();
    const ts = this._data.timestamp;

    if (typeof ts === "number") {
      return BigInt(ts);
    }

    if (ts && typeof ts === "object" && "toString" in ts) {
      return BigInt(ts.toString());
    }

    return 0n;
  }
  
  get priority(): number {
    this.ensureActive();
    return this._data.priority;
  }
  
  get binary(): Uint8Array {
    this.ensureActive();
    return this._binary;
  }
  
  getMetadata(key: string): string | undefined {
    this.ensureActive();
    return this._data.metadata[key];
  }
  
  getAllMetadata(): Readonly<Record<string, string>> {
    this.ensureActive();
    return Object.freeze({ ...this._data.metadata });
  }
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Disposable Implementation (RAII Pattern)
  // ─────────────────────────────────────────────────────────────────────────────
  
  [Symbol.dispose](): void {
    if (this._state === ContextState.Disposed) {
      return; // 이미 폐기됨
    }
    
    // 상태 변경
    this._state = ContextState.Disposed;
    
    // 리소스 정리 로깅
    console.debug(
      `[SovereignContext] Disposed - RequestID: ${this._data.requestId}, ` +
      `TenantID: ${this._data.tenantId}`
    );
    
    // 향후 확장: 커널에 release_context FFI 호출 추가 가능
    // kernel.symbols.release_context(this._binary);
  }
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Internal Helpers
  // ─────────────────────────────────────────────────────────────────────────────
  
  /**
   * 컨텍스트가 활성 상태인지 확인하고, 아니면 에러를 throw합니다.
   */
  private ensureActive(): void {
    if (this._state === ContextState.Disposed) {
      throw new Error(
        `[SovereignContext] Cannot access disposed context. ` +
        `RequestID: ${this._data.requestId}`
      );
    }
    
    if (this._state === ContextState.Faulted) {
      throw new Error(
        `[SovereignContext] Context is in faulted state. ` +
        `RequestID: ${this._data.requestId}`
      );
    }
  }
  
  // ─────────────────────────────────────────────────────────────────────────────
  // Debug & Inspection
  // ─────────────────────────────────────────────────────────────────────────────
  
  /**
   * 디버깅용 문자열 표현.
   */
  toString(): string {
    return (
      `SovereignContext(` +
      `requestId=${this._data.requestId}, ` +
      `tenantId=${this._data.tenantId}, ` +
      `state=${this._state}` +
      `)`
    );
  }
  
  /**
   * 구조화된 JSON 표현 (로깅용).
   */
  toJSON() {
    return {
      requestId: this._data.requestId,
      tenantId: this._data.tenantId,
      traceId: this._data.traceId,
      isTurboMode: this._data.isTurboMode,
      timestamp: this._data.timestamp,
      priority: this._data.priority,
      state: this._state,
      metadata: this._data.metadata,
    };
  }
  
  /**
   * 컨텍스트의 현재 상태를 반환합니다 (internal use).
   * 
   * @internal
   */
  get _internalState(): ContextState {
    return this._state;
  }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [4] Protobuf Encoding (for FFI calls)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/**
 * ContextOptions를 Protobuf로 인코딩합니다.
 * 
 * @param options - 컨텍스트 옵션
 * @returns 직렬화된 바이너리
 * 
 * @internal ContextFactory에서 사용
 */
export function encodeContextOptions(options: ContextOptions): Uint8Array {
  const payload = {
    request_id: options.requestId || crypto.randomUUID(),
    tenant_id: options.tenantId,
    priority: options.priority ?? 5,
    is_turbo_mode: options.isTurboMode ?? false,
    trace_id: options.traceId || crypto.randomUUID(), // 👈 이제 정상 작동
    timestamp: Date.now(),
    metadata: options.metadata || {},
  };

  const message = KrepisContextProto.create(payload);
  return KrepisContextProto.encode(message).finish();
}