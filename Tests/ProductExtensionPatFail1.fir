type Foo(x: U32, y: U32)

main():
    let foo = Foo(x = 1, y = 2)
    match foo:
        Foo(x, y, z, ..):
            print(x)

# expected exit status: 101
# expected stderr:
# Tests/ProductExtensionPatFail1.fir:6:9: Constructor doesn't take named argument 'z'
