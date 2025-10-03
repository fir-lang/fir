main():
    let x = Option.Some("hi")
    if not (x is Option.Some(a)):
        print(x)
        print(a)

# expected exit status: 101
# expected stderr: tests/IsExprFail4.fir:5:15: Unbound variable a
