#!/bin/bash

# A helper to run Peg.fir with the right interpreter flags.

set -e
set -x

cargo run --bin fir --release -- Tool/Peg/Peg.fir -- $@
