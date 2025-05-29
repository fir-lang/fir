type Test[varRowVar, recRowRec]:
    variant: [..varRowVar]
    record: (..recRowRec)

main()
    let x: Test[row[Foo], row(a: U32)] = Test(variant = ~Foo, record = (a = 123u32))

    match x.variant:
        ~Foo: printStr("OK")

    printStr(x.record.a.toStr())

# expected stdout:
# OK
# 123
