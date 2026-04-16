type Foo(
    a: Str,
    b: Str,
)


test(foo: Foo):
    print("Lib/Foo(a = `foo.a`, b = `foo.b`)")
