foo() Option[U32]:
    Option.None


f1():
    match foo():
        Option[U32].Some(x): print(x)
        Option[U32].None: ()


f2():
    match foo():
        Option.Some[U32](x): print(x)
        Option.None[U32]: ()


main():
    f1()
    f2()
