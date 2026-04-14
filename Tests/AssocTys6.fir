trait Foo[t]:
    type A

    getA() Foo[t].A

impl Foo[U32]:
    type A = U64

    getA() Foo[U32].A:
        u64(123)

# Associated type selection with rigid type variable should unify with itself.
makeVar[Foo[t]](a: Foo[t].A) Foo[t].A:
    a

main():
    print(Foo.getA[U32, []]())

# expected stdout:
# 123
