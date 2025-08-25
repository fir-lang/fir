#!/bin/bash

SCRIPT_DIR="$(dirname "$0")"

cargo build --release 2>/dev/null

exit_code=0

for f in "$@"; do
    if [ $# -gt 1 ]; then
        echo "$f"
    fi

    ./target/release/fir -iCompiler=compiler -iPeg=tools/peg compiler/Format.fir -- "$f"

    if [ $? -ne 0 ]; then
        exit_code=1
    fi
done

exit $exit_code
