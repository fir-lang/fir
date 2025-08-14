#!/bin/bash

# A helper to run Peg.fir with the right interpreter flags.

set -e
set -x

cargo run --release -- -iCompiler=compiler -iPeg=tools/peg tools/peg/Peg.fir -- $@
