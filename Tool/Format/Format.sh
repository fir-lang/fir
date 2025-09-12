#!/bin/bash

shopt -s globstar

echo "Building Fir..."
cargo build --release

TEMP_DIR=$(mktemp -d)
# trap 'echo "Cleaning up temp dir"; rm -rf "$TEMP_DIR"' EXIT

echo "Formatted code generated to $TEMP_DIR"

script_failed=0

for file in "$@"; do
  echo "$file"

  OUTPUT_FILE="$TEMP_DIR/$file"
  mkdir -p "$(dirname "$OUTPUT_FILE")"

  # Note: we can't use Format.sh here as it drops the golden test expectations
  # before calling the formatter.
  if ! ./target/release/fir Tool/Format/Format.fir -- "$file" > "$OUTPUT_FILE"; then
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
