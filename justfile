show_recipes:
    @just --list

format:
    cargo fmt

check_rust_formatting:
    cargo fmt --all --check

format_fir_changes:
    ./Tool/Format/FormatChanges.sh

lint:
    cargo clippy --all-targets --all -- -Dwarnings

check:
    cargo check

watch:
    echo src/parser.lalrpop | entr -r lalrpop src/parser.lalrpop & cargo watch

test: build interpreter_unit_test interpreter_golden_test compiler_unit_test compiler_golden_test formatter_golden_test

interpreter_unit_test:
    cargo test

interpreter_golden_test: build
    goldentests target/debug/fir tests '# '

c_golden_test: build
    goldentests target/debug/fir2c tests '# ' --glob='!tests/interpreter/*'

interpreter_update_goldens: build
    goldentests target/debug/fir tests '# ' --overwrite

    # goldentests leaves two newlines at the end of the files, remove one of
    # them.
    for f in tests/**/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done

compiler_unit_test: build_compiler
    ./target/Compiler Compiler/Main.fir
    ./Compiler/tests/tokenize.sh
    ./Compiler/tests/scan.sh
    ./Compiler/tests/parse.sh

compiler_parser_test:
    ./Compiler/tests/parse.sh

compiler_golden_test: build
    goldentests target/debug/fir Tool/Peg/Tests.fir '# '
    goldentests target/debug/fir Compiler/DeriveEq.fir '# '
    goldentests target/debug/fir Compiler/DeriveToDoc.fir '# '

compiler_update_goldens:
    goldentests target/debug/fir Tool/Peg/Tests.fir '# ' --overwrite
    goldentests target/debug/fir Compiler/DeriveEq.fir '# ' --overwrite
    goldentests target/debug/fir Compiler/DeriveToDoc.fir '# ' --overwrite

    # goldentests leaves two newlines at the end of the files, remove one of
    # them.
    for f in Compiler/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done
    for f in Tool/Peg/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done

format_repo:
    ./Tool/Format/FormatRepo.sh

# Note: This command is not ideal for using outside of CI as it updates the
# files in-place relies on `git status` to report formatting changes. In the
# future we probably want a flag in the formatter to signal changes via the
# exit code.
check_fir_formatting: format_repo
    git -P diff
    ! git status --porcelain | grep -q '^ M'

formatter_golden_test:
    goldentests Tool/Format/FormatGoldenTest.sh Tool/Format/tests '# '

formatter_update_goldens:
    goldentests Tool/Format/FormatGoldenTest.sh Tool/Format/tests '# ' --overwrite
    for f in Tool/Format/tests/*.fir; do sed -i -e ':a' -e '/^\n*$/{$d;N;ba' -e '}' -e '$a\' "$f"; done

build:
    cargo build

build_tools:
    mkdir -p target

    set -x

    cargo run --bin fir2c -- Tool/Format/Format.fir --no-run > target/Format.c
    gcc target/Format.c -o target/Format -O3

    cargo run --bin fir2c -- Tool/Peg/Peg.fir --no-run > target/Peg.c
    gcc target/Peg.c -o target/Peg -O3

build_compiler:
    mkdir -p target

    set -x

    cargo run --release --bin fir2c -- Compiler/Main.fir --no-run > target/Compiler.c
    gcc target/Compiler.c -o target/Compiler -O3

generate_parser:
    lalrpop src/parser.lalrpop
    cargo fmt -- src/parser.rs

update_generated_files:
    #!/usr/bin/env bash
    shopt -s globstar

    lalrpop src/parser.lalrpop

    if [ ! -f "target/Peg" ]; then
        # We deliberately don't build Peg ourselves to allow formatting the repo
        # while the code is not in a buildable state, or buggy, or incomplete.
        echo "Error: target/Format isn't build. Build it first with:"
        echo "    just build_tools"
        exit 1
    fi

    generated=()

    for f in **/*.peg; do
        target="${f%.peg}.fir"
        generated+=($target)
        ./target/Peg $f > $target
    done

    Tool/Format/Format.sh "${generated[@]}"

check_generated_files: update_generated_files
    git -P diff
    ! git status --porcelain | grep -q '^ M'

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
