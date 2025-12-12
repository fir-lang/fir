#!/bin/bash

# This script needs to run in Fir git repo root.

shopt -s globstar

echo "Building Fir..."
cargo build --release

script_failed=0

for file in "$@"; do
  echo "$file"

  output_file="$file.formatted"

  if ./target/release/fir Tool/Format/Format.fir -- "$file" > "$output_file"; then
    mv "$output_file" "$file"
  else
    script_failed=1
  fi
done

exit "$script_failed"
