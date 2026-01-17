#!/bin/bash

# This script needs to run in Fir git repo root.

shopt -s globstar

if [ ! -f "target/Format" ]; then
  # We deliberately don't build it ourselves to allow formatting the repo while
  # the code is not in a buildable state, buggy, incomplete.
  echo "Error: target/Format isn't build. Build it first with:"
  echo "    just build_tools"
  exit 1
fi

script_failed=0

for file in "$@"; do
  echo "$file"

  output_file="$file.formatted"

  if ./target/Format "$file" > "$output_file"; then
    mv "$output_file" "$file"
  else
    script_failed=1
  fi
done

exit "$script_failed"
