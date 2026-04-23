type MyResult[t] = Result[Str, t]


main():
    let x = MyResult.Ok[U32](123)

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/SynonymConsFail1.fir:5:13: Constructor type arguments not allowed with synonyms
