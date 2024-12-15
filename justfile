export FIR_ROOT := justfile_directory()

show_recipes:
    @just --list

format:
    cargo fmt

lint:
    cargo clippy --all-targets

test:
    cargo build
    cargo test

    goldentests target/debug/fir tests '# '
    goldentests target/debug/fir examples '# '

update_tests:
    goldentests target/debug/fir tests '# ' --overwrite
    goldentests target/debug/fir examples '# ' --overwrite

# build_site tested with:
#
# - wasm-pack 0.12.1
# - wasm-opt version 114 (version_114-3-g5f6594c52)

build_site:
    #!/usr/bin/env bash

    OUT_DIR=../fir-lang.github.io

    wasm-pack build \
        --target web \
        --release \
        --out-dir target/wasm-pack \
        --no-pack \
        --no-typescript

    cp target/wasm-pack/fir.js $OUT_DIR/fir.js
    cp target/wasm-pack/fir_bg.wasm $OUT_DIR/fir_bg.wasm

    # Copy standard library
    rm $OUT_DIR/fir/lib/*
    cp lib/* $OUT_DIR/fir/lib/
