#!/bin/bash

set -e
set -x

for file in tests/*.fir; do
    [ -e "$file" ] || continue
    cargo run -- compiler/Main.fir -- "$file"
done
