#!/bin/bash

cargo build --release

exit_code=0

for f in **/*.fir; do
    echo $f
    compiler_output=$(./target/release/fir compiler/Lexer.fir --main lexerDumpTokens -- "$f")
    interpreter_output=$(./target/release/fir --tokenize "$f")
    diff -u <(echo "$compiler_output") <(echo "$interpreter_output")
    if [ $? -ne 0 ]; then
        exit_code=1
    fi
done

exit $exit_code
