#!/bin/bash

set -e
set -x

cargo build --release

for file in tests/*.fir; do
    [ -e "$file" ] || continue
    ./target/release/fir compiler/Main.fir -- "$file"
done
