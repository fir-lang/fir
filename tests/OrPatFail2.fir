type Foo:
    A(U32, U32)
    B(U32)

main():
    match f():
        Foo.A(x, y) | Foo.B(x): print(x)

f() Foo:
    Foo.B(123)

# expected exit status: 101
# expected stderr:
# tests/OrPatFail2.fir:7:9: Or pattern alternatives bind different set of variables:
#                      Left = x, y
#                      Right = x
