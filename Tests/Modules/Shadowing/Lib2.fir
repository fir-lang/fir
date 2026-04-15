import []


type Foo:
    A
    B


fun(foo: Foo):
    print("Lib2/fun")
    match foo:
        Foo.A: print("  Lib2/Foo.A")
        Foo.B: print("  Lib2/Foo.B")
