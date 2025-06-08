main():
    let x: Option[U32] = Option.None
    let y: Option[U32] = Option.None
    if x is Option.Some(a) and y is Option.Some(a):
        print(a)

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/IsExprFail3.fir:4:8: Left and right exprs in `and` bind same variables: a
