type Point(x: U32, y: U32)

main():
    let rest = (x = u32(2), y = u32(3))
    let p = Point(x = u32(1), ..rest)
    print(p.x)

# expected exit status: 101
# expected stderr: BUG: Duplicate label in record type (x: U32, ..row(x: U32, y: U32))
