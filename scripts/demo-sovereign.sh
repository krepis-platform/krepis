#!/usr/bin/env bash
set -e

echo "🎯 Krepis Sovereign Kernel - Quick Demo"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "This demonstrates:"
echo "  ✓ Rust-controlled Deno runtime"
echo "  ✓ Explicit context injection"
echo "  ✓ Permission system"
echo "  ✓ Zero-copy op system"
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

cargo run --package krepis-kernel 2>&1