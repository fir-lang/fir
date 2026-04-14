type Point(x: U32, y: U32)

getY() (y: U32):
    (y = u32(77))

main():
    let p = Point(x = u32(3), ..getY())
    print(p.x)
    print(p.y)

# expected stdout:
# 3
# 77
