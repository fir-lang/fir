import [Fir/C as C]


main():
    let x = C/Int


# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/C/ExternTypeAliasIsNotValueFail.fir:9:13: Type Int has no constructor and cannot be used as a value
