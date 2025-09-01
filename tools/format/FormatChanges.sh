#!/bin/bash

TEMP_DIR=$(mktemp -d)
trap 'rm -rf "$TEMP_DIR"' EXIT

script_failed=0

for file in $(git status --porcelain | awk '{print $2}' | grep '\.fir$'); do
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
  rsync -a "$TEMP_DIR/" .
fi

exit "$script_failed"
