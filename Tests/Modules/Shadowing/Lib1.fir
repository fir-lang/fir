import [Tests/Modules/Shadowing/Lib2]


# Shadows `Lib2/Foo`.
type Foo:
    A
    B


fun(foo: Foo):
    print("Lib1/foo")
    match foo:
        Foo.A: print("  Lib1/Foo.A")
        Foo.B: print("  Lib1.Foo.B")
