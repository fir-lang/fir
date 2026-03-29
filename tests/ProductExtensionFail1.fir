type Foo[extras: Row[Rec]](
    x: U32,
    y: U32,
    ..extras
)

main():
    let foo = Foo(x = 123)

# expected exit status: 101
# expected stderr:
# tests/ProductExtensionFail1.fir:8:15: Unable to unify (x: U32) with (x: U32, y: U32, .._1)
