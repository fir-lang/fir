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
    cargo run -- compiler/Main.fir

compiler_golden_test:
    goldentests target/debug/fir compiler/PegTests.fir '# '
    goldentests target/debug/fir compiler/TypeGrammarTest.fir '# '
    goldentests target/debug/fir compiler/DeriveEq.fir '# '

compiler_update_goldens:
    goldentests target/debug/fir compiler/PegTests.fir '# ' --overwrite
    goldentests target/debug/fir compiler/TypeGrammarTest.fir '# ' --overwrite
    goldentests target/debug/fir compiler/DeriveEq.fir '# ' --overwrite

build: generate_parser
    cargo build

generate_parser:
    lalrpop src/parser.lalrpop
    cargo fmt -- src/parser.rs

update_generated_files:
    #!/usr/bin/env bash
    lalrpop src/parser.lalrpop
    tools/peg/Peg.sh compiler/TestGrammar.peg > compiler/TestGrammar.fir
    tools/peg/Peg.sh compiler/TypeGrammar.peg > compiler/TypeGrammar.fir

    # We can't redirect PegGrammar.peg compilation output to PegGrammar.fir, as
    # the PEG compiler itself uses the file. Save the output to a local and
    # then update the file.
    output=$(tools/peg/Peg.sh tools/peg/PegGrammar.peg)
    if [ $? -eq 0 ]; then
        echo "$output" > tools/peg/PegGrammar.fir
    else
        echo "cargo run failed"
        exit 1
    fi

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
