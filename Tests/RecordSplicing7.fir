f(r: (x: U32, y: U32)):
    print(r.x)
    print(r.y)

main():
    let base = (y = u32(99))
    f((x = u32(1), ..base))

# expected stdout:
# 1
# 99
