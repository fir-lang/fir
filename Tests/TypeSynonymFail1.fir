type Foo = Foo

main():
    let x: Foo = 1

# expected exit status: 101
# expected stderr: Type synonym cycle detected: Foo
