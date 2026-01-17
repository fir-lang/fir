#!/bin/bash

# This script needs to run in Fir git repo root.

set -e

shopt -s globstar

SCRIPT_DIR="$(dirname "$0")"

mkdir -p target
cargo run --bin fir2c -- Compiler/Parser.fir --no-run > target/Parser.c
gcc target/Parser.c -o target/Parser -O3

exit_code=0

skip_files=()

source "${SCRIPT_DIR}/common.sh"

for f in "${files[@]}"; do
    echo $f
    ./target/Parser "$f"
    if [ $? -ne 0 ]; then
        exit_code=1
    fi
done

exit $exit_code
