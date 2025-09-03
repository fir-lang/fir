#!/bin/bash

set -e

changes=$(git status --porcelain | awk '{print $2}' | grep '\.fir$')

./tools/format/Format.sh $changes
