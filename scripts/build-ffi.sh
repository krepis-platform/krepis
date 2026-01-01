#!/usr/bin/env bash
set -e

echo "🔨 Building Krepis Sovereign Infrastructure..."

# Build Rust kernel with cdylib
echo "📦 Compiling Rust kernel (cdylib)..."
cargo build --release --package krepis-kernel

# Verify FFI symbols
echo "🔍 Verifying FFI exports..."
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    nm -D target/release/libkrepis_kernel.so | grep -E "initialize_kernel|create_context|free_buffer"
elif [[ "$OSTYPE" == "darwin"* ]]; then
    nm -g target/release/libkrepis_kernel.dylib | grep -E "initialize_kernel|create_context|free_buffer"
fi

# Run Rust tests
echo "🧪 Running Rust tests..."
cargo test --package krepis-kernel

# Set kernel path for Deno
export KREPIS_KERNEL_PATH="$(pwd)/target/release/libkrepis_kernel.so"
if [[ "$OSTYPE" == "darwin"* ]]; then
    export KREPIS_KERNEL_PATH="$(pwd)/target/release/libkrepis_kernel.dylib"
fi

# Run Deno FFI tests
echo "🧪 Running Deno FFI tests..."
deno test --allow-all --allow-ffi packages/core/tests/ffi_test.ts

echo "✅ Build complete!"
echo "📍 Kernel: $KREPIS_KERNEL_PATH"