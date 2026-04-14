# For now `()` and omitting the field lists are the same thing.
#
# In the future we may want to only allow one of these.

type MyUnit()

type Foo:
    Foo()

main():
    let unit = MyUnit
    f(unit)

    let foo = Foo.Foo
    g(foo)

f(x: MyUnit): ()
g(x: Foo): ()
