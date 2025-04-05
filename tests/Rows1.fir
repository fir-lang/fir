test[RecRow[r]](r: (x: I32, y: I32, ..r))
    printStr(r.x.toStr())
    printStr(r.y.toStr())

id[RecRow[r]](r: (x: I32, ..r)): (x: I32, ..r)
    printStr(r.x.toStr())
    r

type Test[recRow]:
    x: (x: I32, ..recRow)

main()
    test(id((x = 1, y = 2)))
    test(id((x = 3, y = 4, z = "hi")))
    let struct = Test(x = (x = 123, y = 456))
    test(id(struct.x))

# expected stdout:
# 1
# 1
# 2
# 3
# 3
# 4
# 123
# 123
# 456
