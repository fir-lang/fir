type Foo[extras: Row[Rec]](
    x: U32,
    ..extras
)

main():
    let foo = Foo(x = 1, b = Bool.True)
    match foo:
        Foo(b = Bool.True, ..):
            print("true")
        Foo(b = Bool.False, ..):
            print("false")

# expected stdout:
# true
