#!/bin/bash

shopt -s globstar

TEMP_DIR=$(mktemp -d)
# trap 'echo "Cleaning up temp dir"; rm -rf "$TEMP_DIR"' EXIT

echo "Formatted code generated to $TEMP_DIR"

found_files=0
for file in compiler/**/*.fir lib/**/*.fir tools/**/*.fir; do
  # Skip test directories.
  if [[ "$file" == *"/"tests"/"* || "$file" == "tests/"* ]]; then
    continue
  fi

  echo "$file"

  OUTPUT_FILE="$TEMP_DIR/$file"
  mkdir -p "$(dirname "$OUTPUT_FILE")"
  ./tools/format/Format.sh "$file" > "$OUTPUT_FILE"

  if ! ./tools/format/Format.sh "$file" > "$OUTPUT_FILE"; then
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
