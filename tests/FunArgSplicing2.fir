type Point(x: U32, y: U32)

main():
    let rest = (y = u32(100))
    let p = Point(x = u32(5), ..rest)
    print(p.x)
    print(p.y)

# expected stdout:
# 5
# 100
