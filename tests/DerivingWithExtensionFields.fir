#[derive(Eq, ToDoc)]
type T1[t](
    msg: Str,
    ..t
)

#[derive(Eq, ToDoc)]
type T2[e1, e2]:
    A(x: U32, ..e1)
    B(y: U32, ..e2)

main():
    let t1 = T1(msg = "hello")
    printStr(t1.toDoc().render(80))

    let t1b = T1(msg = "hello")
    printStr((t1 == t1b).toStr())

    let t2a = T2.A(x = u32(42))
    let t2b = T2.B(y = u32(99))
    printStr(t2a.toDoc().render(80))
    printStr((t2a == t2a).toStr())
    printStr((t2a == t2b).toStr())

# expected stdout:
# T1(msg = "hello", ())
# Bool.True
# T2.A(x = 42, ())
# Bool.True
# Bool.False
