main():
    let x: Option[U32] = Option.None
    if x is Option.Some(a) or Bool.True:
        print(a)

# expected exit status: 101
# expected stderr: Tests/IsExprFail2.fir:4:15: Unbound variable a
