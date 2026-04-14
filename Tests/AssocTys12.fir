# Test that an associated type can be inferred from context without an explicit
# type annotation, assigning the result of a method returning `Foo[t].Item` to a
# concrete type unifies the associated type correctly.

trait Foo[t]:
    type Item

    getItem(self: t) Foo[t].Item

type MyType:
    MyType

impl Foo[MyType]:
    type Item = I32

    getItem(self: MyType) Foo[MyType].Item:
        42

main():
    # No explicit type annotation on `x`, the associated type should resolve
    # through unification when we pass `x` to `print` (which needs `ToStr`).
    let x = MyType.MyType.getItem()
    print(x)

# expected stdout:
# 42
