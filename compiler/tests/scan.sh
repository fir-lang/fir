#!/bin/bash

SCRIPT_DIR="$(dirname "$0")"

cargo build --release

exit_code=0

# These files have wide (as in "displayed width" defined my unicode)
# characters, and we don't have a Fir library yet to get character widths and
# update columns properly with wide chars.
skip_files=(
    "tests/Char.fir"
    "tests/StrBuf.fir"
)

source "${SCRIPT_DIR}/common.sh"

for f in "${files[@]}"; do
    echo $f
    compiler_output=$(./target/release/fir compiler/Scanner.fir --main scannerDumpTokens -- "$f")
    interpreter_output=$(./target/release/fir --scan "$f")
    diff -u <(echo "$interpreter_output") <(echo "$compiler_output")
    if [ $? -ne 0 ]; then
        exit_code=1
    fi
done

exit $exit_code
