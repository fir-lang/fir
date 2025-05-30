export FIR_ROOT := justfile_directory()

show_recipes:
    @just --list

format:
    cargo fmt

lint:
    cargo clippy --all-targets

check:
    cargo check

watch:
    echo src/parser.lalrpop | entr -r lalrpop src/parser.lalrpop & cargo watch

test: build
    cargo test
    goldentests target/debug/fir tests '# '

    cargo run -- compiler/Peg.fir -- compiler/TestGrammar.peg > compiler/TestGrammar.fir
    cargo run -- compiler/Main.fir
    goldentests target/debug/fir compiler/PegTests.fir '# '

# Only run type checking tests.
test_tc: build
    cargo test
    grep -rl -- "--typecheck" tests | xargs -d '\n' -I {} goldentests target/debug/fir {} '# '

update_tc_tests: build
    cargo test
    grep -rl -- "--typecheck" tests | xargs -d '\n' -I {} goldentests target/debug/fir {} '# ' --overwrite

update_tests: build
    goldentests target/debug/fir tests '# ' --overwrite
    goldentests target/debug/fir compiler/PegTests.fir '# ' --overwrite

build: generate_parser
    cargo build

generate_parser:
    lalrpop src/parser.lalrpop
    cargo fmt -- src/parser.rs

update_generated_files:
    lalrpop src/parser.lalrpop
    cargo run -- compiler/Peg.fir -- compiler/TestGrammar.peg > compiler/TestGrammar.fir
    cargo run -- compiler/Peg.fir -- compiler/PegGrammar.peg > compiler/PegGrammar.new.fir
    mv compiler/PegGrammar.new.fir compiler/PegGrammar.fir

# build_site tested with:
#
# - wasm-pack 0.12.1
# - wasm-opt version 114 (version_114-3-g5f6594c52)

build_site: generate_parser
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

    # Copy samples
    cp tests/ErrorHandling.fir $OUT_DIR/ErrorHandling.fir
    cp tests/ThrowingIter.fir $OUT_DIR/ThrowingIter.fir
    cp tests/PPrintExample.fir $OUT_DIR/PPrintExample.fir
