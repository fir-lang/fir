main():
    let base = (y = u32(100))
    let r: (x: U32, y: U32) = (x = u32(1), ..base)
    print(r.x)
    print(r.y)

# expected stdout:
# 1
# 100
