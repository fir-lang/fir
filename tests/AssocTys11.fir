# Test that two traits with the same associated type name don't interfere.

trait Foo[t]:
    type Item

    fooItem(self: t) Foo[t].Item

trait Bar[t]:
    type Item

    barItem(self: t) Bar[t].Item

type MyType:
    MyType

impl Foo[MyType]:
    type Item = I32

    fooItem(self: MyType) Foo[MyType].Item:
        42

impl Bar[MyType]:
    type Item = Str

    barItem(self: MyType) Bar[MyType].Item:
        "hello"

main():
    let x = MyType.MyType
    let a: I32 = x.fooItem()
    let b: Str = x.barItem()
    print(a)
    print(b)

# expected stdout:
# 42
# hello
