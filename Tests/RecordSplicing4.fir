main():
    let a = (x = 1)
    let b = (y = 2, ..a)
    let c = (z = 3, ..b)
    print(c.x)
    print(c.y)
    print(c.z)

# expected stdout:
# 1
# 2
# 3
