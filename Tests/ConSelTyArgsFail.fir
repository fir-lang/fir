main():
    print(Option[U32].None[U32])

# expected exit status: 101
# expected stderr:
# Tests/ConSelTyArgsFail.fir:2:11: Constructor selection expressions should have only one type argument list
