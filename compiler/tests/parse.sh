#!/bin/bash

SCRIPT_DIR="$(dirname "$0")"

cargo build --release

exit_code=0

skip_files=()

source "${SCRIPT_DIR}/common.sh"

for f in "${files[@]}"; do
    echo $f
    ./target/release/fir -iCompiler=compiler -iPeg=tools/peg compiler/Parser.fir -- "$f"
    if [ $? -ne 0 ]; then
        exit_code=1
    fi
done

exit $exit_code
