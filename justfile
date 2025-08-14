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

test: build interpreter_unit_test interpreter_golden_test compiler_unit_test compiler_golden_test

interpreter_unit_test:
    cargo test

interpreter_golden_test:
    goldentests target/debug/fir tests '# '

interpreter_update_goldens: build
    goldentests target/debug/fir tests '# ' --overwrite

    # goldentests leaves two newlines at the end of the files, remove one of
    # them.
    for f in tests/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done

compiler_unit_test:
    cargo run -- compiler/Main.fir -iPeg=tools/peg
    ./compiler/tests/tokenize.sh
    ./compiler/tests/scan.sh

compiler_golden_test:
    goldentests target/debug/fir tools/peg/Tests.fir '# '
    goldentests target/debug/fir compiler/DeriveEq.fir '# '

compiler_update_goldens:
    goldentests target/debug/fir tools/peg/Tests.fir '# ' --overwrite
    goldentests target/debug/fir compiler/DeriveEq.fir '# ' --overwrite

    # goldentests leaves two newlines at the end of the files, remove one of
    # them.
    for f in compiler/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done
    for f in tools/peg/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done

build: generate_parser
    cargo build

generate_parser:
    lalrpop src/parser.lalrpop
    cargo fmt -- src/parser.rs

update_generated_files:
    #!/usr/bin/env bash
    lalrpop src/parser.lalrpop

    # We can't redirect PegGrammar.peg compilation output to PegGrammar.fir, as
    # the PEG compiler itself uses the file. Save the output to a local and
    # then update the file.
    output=$(tools/peg/Peg.sh tools/peg/PegGrammar.peg)
    if [ $? -eq 0 ]; then
        echo "$output" > tools/peg/PegGrammar.fir
    else
        echo "generated file update failed"
        exit 1
    fi

    tools/peg/Peg.sh tools/peg/TestGrammar.peg > tools/peg/TestGrammar.fir
    tools/peg/Peg.sh compiler/Grammar.peg > compiler/Grammar.fir

# build_site tested with:
#
# - wasm-bindgen 0.2.100
# - wasm-opt version 123 (version_123-209-g99cf92269)

build_site: generate_parser
    #!/usr/bin/env bash

    set -e
    set -x

    OUT_DIR=../fir-lang.github.io

    # Build Wasm binary.
    cargo build --lib --release --target=wasm32-unknown-unknown

    # Generate JS shims.
    wasm-bindgen target/wasm32-unknown-unknown/release/fir.wasm \
        --out-dir $OUT_DIR --no-typescript --target web

    # Optimize Wasm binary for size.
    wasm-opt --all-features --closed-world --traps-never-happen -Os \
        $OUT_DIR/fir_bg.wasm -o $OUT_DIR/fir_bg.wasm

    # Copy standard library
    rm $OUT_DIR/fir/lib/*
    cp lib/* $OUT_DIR/fir/lib/

    # Copy samples
    cp tests/ErrorHandling.fir $OUT_DIR/ErrorHandling.fir
    cp tests/ThrowingIter.fir $OUT_DIR/ThrowingIter.fir
    cp tests/PPrintExample.fir $OUT_DIR/PPrintExample.fir
