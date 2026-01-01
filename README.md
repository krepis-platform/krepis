# Krepis: Sovereign AI-Native ADaaS Platform

> Architecture Development as a Service - v1.5.0 (The Deterministic Sovereign)

## 🎯 Core Philosophy

**Sovereign Control, Fractal Intelligence**

- **Systemic Rigidity**: Rust + Deno for deterministic runtime
- **Fractal Intelligence**: Master-Expert-Sub AI legion architecture
- **Explicit Context**: Zero implicit state propagation

## 🏗️ Architecture Overview

### Hybrid Sovereign Monorepo

```
krepis/
├── Cargo.toml              # Rust workspace root
├── deno.json               # Deno runtime config
├── crates/
│   ├── krepis-kernel/      # Hyper-Pingora native server (Rust binary)
│   └── krepis-knul/        # KNUL protocol engine (Rust library)
└── packages/
    ├── cli/                # Sovereign Master CLI (Rust binary)
    └── core/               # Trinity Framework Core (TypeScript/Deno)
```

## 🚀 Quick Start

### Prerequisites

- Rust 1.75+ (latest stable)
- Deno 2.0+
- Git

### Installation

```bash
# Clone repository
git clone https://github.com/krepis/krepis.git
cd krepis

# Build Rust components
cargo build --workspace

# Check TypeScript core
deno task check

# Run tests
cargo test --workspace
deno task test
```

## 🔧 Development

### Start Kernel (Native Server)

```bash
cargo run --package krepis-kernel
```

### Start Core (Standard Mode - TS Simulator)

```bash
deno task dev
```

### Build CLI

```bash
cargo build --package krepis-cli --release
```

## 📐 Trinity Pattern Enforcement

All business logic follows:

1. **Hexagonal Architecture**: Adapter isolation
2. **Functional Core**: Pure functions in domain layer
3. **CQS**: Command-Query Separation

## 🧪 Testing

### Rust Tests

```bash
cargo test --workspace
```

### TypeScript Tests

```bash
deno test --allow-all packages/core/tests/
```

### Coverage

```bash
# Rust coverage (requires cargo-tarpaulin)
cargo tarpaulin --workspace --out Html

# Deno coverage
deno test --coverage=./coverage
deno coverage ./coverage
```

## 🔐 Core Principles

### Explicit Context Propagation

Every async function receives `ctx: KrepisContext`:

```typescript
async function processRequest(ctx: KrepisContext, data: RequestData) {
  // All async operations must receive ctx explicitly
}
```

### Zero-Copy FFI

Rust ↔ TypeScript data exchange via Deno FFI:

```typescript
// Shared memory pointer - no copying
const buffer = new Uint8Array(Deno.UnsafePointerView.getArrayBuffer(ptr, size));
```

## 📊 Build Targets

- **Standard Mode**: Pure TypeScript simulator for development
- **Turbo Mode**: Rust native engine for production

## 🛡️ Quality Standards

- Test Coverage: ≥80% (enforced in CI)
- Zero `any` types in TypeScript
- `#![deny(clippy::pedantic)]` in Rust
- No circular dependencies

## 📝 License

Apache-2.0

## 🌐 Links

- Documentation: https://docs.krepis.dev
- API Reference: https://api.krepis.dev
- Community: https://discord.gg/krepis

---

**Status**: Phase 1 - The Sovereign Genesis (v1.5.0)