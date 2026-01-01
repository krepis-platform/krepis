#!/usr/bin/env bash
set -e

echo "🚀 Krepis Sovereign Kernel Build System v2.0.0"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# Build Protobuf schemas
echo "📦 Compiling Protobuf schemas..."
cargo build --package krepis-kernel 2>&1 | grep -E "(Compiling|Finished)" || true

# Run Rust tests
echo ""
echo "🧪 Running Rust tests..."
cargo test --package krepis-kernel --lib

# Run integration tests
echo ""
echo "🔬 Running integration tests..."
cargo test --package krepis-kernel --test sovereign_test

# Build release binary
echo ""
echo "🔨 Building release binary..."
cargo build --release --package krepis-kernel

echo ""
echo "✅ Build complete!"
echo ""
echo "Run the kernel:"
echo "  cargo run --package krepis-kernel"
echo ""
echo "Or run release:"
echo "  ./target/release/krepis-kernel"