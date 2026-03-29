type Foo[extras: Row[Rec]](
    x: U32,
    y: U32,
    ..extras
)

main():
    let foo = Foo(y = 123, z = "hi")

# expected exit status: 101
# expected stderr:
# tests/ProductExtensionFail2.fir:8:15: Unable to unify (y: U32, z: Str) with (x: U32, y: U32, ..row(z: Str, .._2))
