#!/bin/bash

cargo build --release

exit_code=0

# These files have wide (as in "displayed width" defined my unicode)
# characters, and we don't have a Fir library yet to get character widths and
# update columns properly with wide chars.
skip_files=(
    "tests/Char.fir"
    "tests/StrBuf.fir"
)

for f in **/*.fir; do
    skip=false
    for skip_f in "${skip_files[@]}"; do
        if [[ "$f" == "$skip_f" ]]; then
            echo "$f: skipping"
            skip=true
            break
        fi
    done

    if $skip; then
        continue
    fi

    echo $f

    compiler_output=$(./target/release/fir compiler/Lexer.fir --main lexerDumpTokens -- "$f")
    interpreter_output=$(./target/release/fir --tokenize "$f")
    diff -u <(echo "$interpreter_output") <(echo "$compiler_output")
    if [ $? -ne 0 ]; then
        exit_code=1
    fi
done

exit $exit_code
