/**
 * KrepisContext Protobuf Wrapper
 * Zero-copy context propagation via Rust FFI
 */

import { createNativeContext } from "./bindings.ts";

export interface KrepisContextData {
  requestId: string;
  tenantId?: string;
  priority?: number;
  isTurboMode: boolean;
  traceId?: string;
  timestamp?: number;
  metadata?: Record<string, string>;
}

export class KrepisContext {
  private readonly serialized: Uint8Array;
  
  constructor(data: KrepisContextData) {
    this.serialized = createNativeContext(data.requestId, data.isTurboMode);
  }
  
  toBuffer(): Uint8Array {
    return this.serialized;
  }
  
  static create(partial?: Partial<KrepisContextData>): KrepisContext {
    return new KrepisContext({
      requestId: crypto.randomUUID(),
      isTurboMode: false,
      ...partial,
    });
  }
}

export interface KnulConfigData {
  enable0rtt: boolean;
  compressionLevel: number;
  maxStreams: number;
}

export function encodeInitRequest(
  ctx: KrepisContext,
  config: KnulConfigData,
): Uint8Array {
  // Protobuf encoding for InitializeRequest
  // Field 1: KrepisContext (message)
  // Field 2: KnulConfig (message)
  
  const ctxBuffer = ctx.toBuffer();
  
  // Simple protobuf encoding (tag + length + value)
  const result: number[] = [];
  
  // Tag 1 (field 1, wire type 2 = length-delimited)
  result.push(0x0a);
  result.push(ctxBuffer.length);
  result.push(...ctxBuffer);
  
  // Tag 2 (field 2, wire type 2)
  result.push(0x12);
  const configBytes = encodeKnulConfig(config);
  result.push(configBytes.length);
  result.push(...configBytes);
  
  return new Uint8Array(result);
}

function encodeKnulConfig(config: KnulConfigData): number[] {
  const result: number[] = [];
  
  // Field 1: enable_0rtt (bool)
  if (config.enable0rtt) {
    result.push(0x08, 0x01);
  }
  
  // Field 2: compression_level (uint32)
  result.push(0x10, config.compressionLevel);
  
  // Field 3: max_streams (uint32)
  result.push(0x18);
  encodeVarint(config.maxStreams, result);
  
  return result;
}

function encodeVarint(value: number, output: number[]): void {
  while (value > 127) {
    output.push((value & 0x7f) | 0x80);
    value >>>= 7;
  }
  output.push(value);
}

export function decodeInitResponse(buffer: Uint8Array): {
  success: boolean;
  errorMessage: string;
} {
  let pos = 0;
  let success = false;
  let errorMessage = "";
  
  while (pos < buffer.length) {
    const tag = buffer[pos++];
    if (tag === undefined) break;
    
    const fieldNum = tag >> 3;
    
    if (fieldNum === 1) {
      const val = buffer[pos++];
      if (val !== undefined) {
        success = val === 1;
      }
    } else if (fieldNum === 2) {
      const len = buffer[pos++];
      if (len !== undefined) {
        const end = pos + len;
        if (end <= buffer.length) {
          errorMessage = new TextDecoder().decode(buffer.slice(pos, end));
          pos = end;
        }
      }
    } else {
      // 알 수 없는 필드는 스킵 (Protobuf 표준 가이드)
      // 실제 구현에서는 wire type에 따라 적절한 바이트만큼 pos를 이동시켜야 합니다.
      break; 
    }
  }
  
  return { success, errorMessage };
}