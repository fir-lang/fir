type MyResult[t] = Result[Str, t]


main():
    let x = MyResult[Str, U32].Ok(123)

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/SynonymConsFail2.fir:5:13: Type MyResult takes 1 arguments, but passed 2
