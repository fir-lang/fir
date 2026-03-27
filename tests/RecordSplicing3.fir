main():
    let base = (x = 10, y = 20)
    let extended = (z = 30, ..base)
    print(extended.x)
    print(extended.y)
    print(extended.z)

# expected stdout:
# 10
# 20
# 30
