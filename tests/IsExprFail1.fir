main():
    let x: Option[U32] = Option.None
    if x is Option.Some(a) || a == 0:
        ()

# args: --no-backtrace
# expected exit status: 101
# expected stderr: tests/IsExprFail1.fir:3:31: Unbound variable a
