type Foo[extras](
    x: U32,
    y: U32,
    ..extras
)

main():
    let foo = Foo(x = 123)

# expected exit status: 101
# expected stderr:
# tests/ProductExtensionFail1.fir:8:15: Function with minimum arity 2 is passed 1 args
