#!/bin/bash

# Production Build
cargo build -p krepis-twin --release \
    --no-default-features --features production \
    --target-dir target/production

# Twin Build
cargo build -p krepis-twin --release \
    --features twin \
    --target-dir target/twin