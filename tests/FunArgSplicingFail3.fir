type Point(x: U32, y: U32, z: U32)

main():
    let rest = (y = u32(2))
    let p = Point(x = u32(1), ..rest)
    print(p.x)

# expected exit status: 101
# expected stderr:
# tests/FunArgSplicingFail3.fir:5:13: Unable to unify (x: U32, y: U32) with (x: U32, y: U32, z: U32)
