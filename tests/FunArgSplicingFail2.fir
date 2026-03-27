type Point(x: U32, y: U32)

main():
    let rest = (y = "wrong")
    let p = Point(x = u32(1), ..rest)
    print(p.x)

# expected exit status: 101
# expected stderr: tests/FunArgSplicingFail2.fir:5:13: Unable to unify types Str and U32
