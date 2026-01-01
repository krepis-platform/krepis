/**
 * Krepis Kernel FFI Bindings v1.5.0
 * Zero-copy native bridge via Deno FFI
 */

const KERNEL_LIB_PATH = Deno.env.get("KREPIS_KERNEL_PATH") || 
  "./target/release/libkrepis_kernel.so";

const symbols = {
  initialize_kernel: {
    parameters: ["pointer", "usize"],
    result: "pointer",
  },
  create_context: {
    parameters: ["pointer", "usize", "bool"],
    result: "pointer",
  },
  free_buffer: {
    parameters: ["pointer"],
    result: "void",
  },
} as const satisfies Deno.ForeignLibraryInterface;

let kernel: Deno.DynamicLibrary<typeof symbols> | null = null;

export function loadKernel(): void {
  if (kernel) return;
  try {
    kernel = Deno.dlopen(KERNEL_LIB_PATH, symbols);
    console.log("✅ Kernel FFI loaded:", KERNEL_LIB_PATH);
  } catch (error) {
    console.error("❌ Failed to load kernel:", error);
    throw error;
  }
}

export function initializeKernel(buffer: Uint8Array): Uint8Array {
  if (!kernel) loadKernel();
  
  const ptr = kernel!.symbols.initialize_kernel(
    Deno.UnsafePointer.of(buffer as Uint8Array<ArrayBuffer>),
    BigInt(buffer.length),
  );
  
  if (!ptr) throw new Error("Kernel initialization failed");
  
  return readAndFreeBuffer(ptr);
}

export function createNativeContext(requestId: string, isTurbo: boolean): Uint8Array {
  if (!kernel) loadKernel();
  
  const encoder = new TextEncoder();
  const requestIdBytes = encoder.encode(requestId);
  
  const ptr = kernel!.symbols.create_context(
    Deno.UnsafePointer.of(requestIdBytes as Uint8Array<ArrayBuffer>),
    BigInt(requestIdBytes.length),
    isTurbo,
  );
  
  if (!ptr) throw new Error("Context creation failed");
  
  return readAndFreeBuffer(ptr);
}

export function unloadKernel(): void {
  if (kernel) {
    kernel.close();
    kernel = null;
  }
}

function readAndFreeBuffer(ptr: Deno.PointerObject): Uint8Array {
  const view = new Deno.UnsafePointerView(ptr);
  
  // 핵심 교정: Rust의 repr(C) 구조체 정렬(Alignment) 확인
  // 64비트 시스템에서 *mut u8(8) + usize(8) + usize(8)
  const dataAddr = view.getBigUint64(0);
  const dataPtr = Deno.UnsafePointer.create(dataAddr);
  const rawLen = view.getBigUint64(8); // 이 값이 비정상적으로 읽히는 중

  // 디버깅 로그 추가 (터미널에서 실제 숫자를 확인하기 위함)
  // console.log(`[FFI Debug] Ptr: ${dataAddr}, Len: ${rawLen}`);

  if (rawLen > 2147483647n) { // 2GB 이상이면 데이터 오염으로 판단
    throw new Error(`FFI Protocol Violation: Abnormal length ${rawLen}`);
  }
  
  const len = Number(rawLen);
  if (!dataPtr || len === 0) {
    kernel!.symbols.free_buffer(ptr);
    return new Uint8Array(0);
  }

  const response = new Uint8Array(len);
  // getArrayBuffer 대신 안전한 copyInto 사용 권장
  Deno.UnsafePointerView.copyInto(dataPtr, response);
  
  kernel!.symbols.free_buffer(ptr);
  return response;
}