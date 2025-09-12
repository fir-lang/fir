#!/bin/bash

# This script is used for testing and it drops the golden test expectations
# before running the formatter (in a temporary file), which are assumed to be
# at the end of the file (argument to this script) and start with
# '# expected stdout:'.

set -e

SCRIPT_DIR="$(dirname "$0")"

cargo build --release 2>/dev/null

exit_code=0

output_file=$(mktemp)
trap 'rm -rf "$output_file"' EXIT

for f in "$@"; do
    if [ $# -gt 1 ]; then
        echo "$f"
    fi

    contents_without_test_expectations=$(sed '/^# expected stdout:/,$d' "$f")
    echo "$contents_without_test_expectations" > "$output_file"

    ./target/release/fir Tool/Format/Format.fir -- "$output_file"

    if [ $? -ne 0 ]; then
        exit_code=1
    fi
done

exit $exit_code
