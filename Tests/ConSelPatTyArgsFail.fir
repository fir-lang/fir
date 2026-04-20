foo() Option[U32]:
    Option.None


f3():
    match foo:
        Option[U32].Some[U32](x): print(x)
        _: ()


main():
    f3()

# expected exit status: 101
# expected stderr:
# Tests/ConSelPatTyArgsFail.fir:7:9: Constructor selection expressions should have only one type argument list
