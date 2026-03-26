type Foo[extras](
    x: U32,
    y: U32,
    ..extras
)

main():
    let foo = Foo(y = 123, z = "hi")

# expected exit status: 101
# expected stderr:
# tests/ProductExtensionFail2.fir:8:15: Missing required arguments: {"x"}
