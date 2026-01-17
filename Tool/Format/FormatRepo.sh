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

TEMP_DIR=$(mktemp -d)
# trap 'echo "Cleaning up temp dir"; rm -rf "$TEMP_DIR"' EXIT

echo "Formatted code generated to $TEMP_DIR"

script_failed=0

for file in Compiler/**/*.fir Fir/**/*.fir Tool/**/*.fir; do
  # Skip test directories.
  if [[ "$file" == *"/"tests"/"* || "$file" == "tests/"* ]]; then
    continue
  fi

  echo "$file"

  output_file="$TEMP_DIR/$file"
  mkdir -p "$(dirname "$output_file")"

  # Note: we can't use Format.sh here as it drops the golden test expectations
  # before calling the formatter.
  if ! ./target/Format "$file" > "$output_file"; then
    script_failed=1
  fi
done

if [ "$script_failed" -ne 0 ]; then
  echo "Formatting failed, see errors above."
  echo "NOT copying formatted files to working directory."
else
  echo "Copying formatted files to working directory..."
  rsync -a "$TEMP_DIR/" .
  echo "Done."
fi

exit "$script_failed"
