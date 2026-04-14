type Point(x: U32, y: U32)

main():
    let args = (x = u32(42), y = u32(99))
    let p = Point(..args)
    print(p.x)
    print(p.y)

# expected stdout:
# 42
# 99
