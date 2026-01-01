#!/usr/bin/env bash
set -e

echo "🔄 Krepis Sovereign Journal - Recovery Demo"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""
echo "This demonstrates persistent state across kernel restarts:"
echo "  ✓ Sled DB transaction journaling"
echo "  ✓ Atomic counter increments"
echo "  ✓ Crash recovery"
echo ""

# Clean previous state
if [ -d ".krepis" ]; then
    echo "🧹 Cleaning previous storage..."
    rm -rf .krepis
fi

echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📍 FIRST RUN - Initial state"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

cargo run --package krepis-kernel 2>&1 | grep -E "(Recovery|Op count|Journal entries)"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📍 SECOND RUN - Recovery from disk"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

cargo run --package krepis-kernel 2>&1 | grep -E "(Recovery|Op count|Journal entries)"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "✅ Recovery test complete!"
echo ""
echo "Expected behavior:"
echo "  - First run:  Recovery: 0 ops"
echo "  - Second run: Recovery: 3 ops (from first run)"
echo "  - Second run final: 6 ops total (3 recovered + 3 new)"