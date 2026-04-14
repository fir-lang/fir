trait Foo[t]:
    type A

    getA() Foo[t].A

impl Foo[U32]:
    type A = U64

    getA() Foo[U32].A:
        u64(123)

main():
    let x: U64 = Foo.getA[U32, []]()
    print(x)

# expected stdout:
# 123
