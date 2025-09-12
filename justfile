show_recipes:
    @just --list

format:
    cargo fmt

format_fir_changes:
    ./Tool/Format/FormatChanges.sh

lint:
    cargo clippy --all-targets

check:
    cargo check

watch:
    echo src/parser.lalrpop | entr -r lalrpop src/parser.lalrpop & cargo watch

test: build interpreter_unit_test interpreter_golden_test compiler_unit_test compiler_golden_test formatter_golden_test

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
    cargo run -- Compiler/Main.fir
    ./Compiler/tests/tokenize.sh
    ./Compiler/tests/scan.sh

compiler_golden_test:
    goldentests target/debug/fir Tool/Peg/Tests.fir '# '
    goldentests target/debug/fir Compiler/DeriveEq.fir '# '

compiler_update_goldens:
    goldentests target/debug/fir Tool/Peg/Tests.fir '# ' --overwrite
    goldentests target/debug/fir Compiler/DeriveEq.fir '# ' --overwrite

    # goldentests leaves two newlines at the end of the files, remove one of
    # them.
    for f in Compiler/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done
    for f in Tool/Peg/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done

formatter_golden_test:
    goldentests Tool/Format/FormatGoldenTest.sh Tool/Format/tests '# '

formatter_update_goldens:
    goldentests Tool/Format/FormatGoldenTest.sh Tool/Format/tests '# ' --overwrite
    for f in Tool/Format/tests/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done

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
    output=$(Tool/Peg/Peg.sh Tool/Peg/PegGrammar.peg)
    if [ $? -eq 0 ]; then
        echo "$output" > Tool/Peg/PegGrammar.fir
    else
        echo "generated file update failed"
        exit 1
    fi

    Tool/Peg/Peg.sh Tool/Peg/TestGrammar.peg > Tool/Peg/TestGrammar.fir
    Tool/Peg/Peg.sh Compiler/Grammar.peg > Compiler/Grammar.fir

    Tool/Format/Format.sh Tool/Peg/{PegGrammar,TestGrammar}.fir Compiler/Grammar.fir

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
    rm -rf $OUT_DIR/Fir
    cp -r Fir $OUT_DIR/

    # Copy samples
    cp tests/ErrorHandling.fir $OUT_DIR/ErrorHandling.fir
    cp tests/ThrowingIter.fir $OUT_DIR/ThrowingIter.fir
    cp tests/PPrintExample.fir $OUT_DIR/PPrintExample.fir
