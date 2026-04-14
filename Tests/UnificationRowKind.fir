type Foo:
    Foo

type Test[varRow, recRow](
    variant: [..varRow],
    record: (..recRow),
)

main():
    let x: Test[row[Foo], row(a: U32)] = Test(variant = ~Foo.Foo, record = (a = u32(123)))

    match x.variant:
        ~Foo.Foo: printStr("OK")

    printStr(x.record.a.toStr())

# expected stdout:
# OK
# 123
