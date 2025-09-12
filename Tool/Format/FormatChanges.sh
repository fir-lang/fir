#!/bin/bash

set -e

changes=$(git status --porcelain | awk '{print $2}' | grep '\.fir$')

./Tool/Format/Format.sh $changes
