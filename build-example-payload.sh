#!/bin/sh

RUSTFLAGS="-C link-arg=-Texample-payload/src/memory.ld" cargo build --target=riscv32i-unknown-none-elf --profile minimal -p example-payload
