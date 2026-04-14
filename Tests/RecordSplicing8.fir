main():
    let base = (y = 2)
    let (x = a, y = b) = (x = 1, ..base)
    print(a)
    print(b)

# expected stdout:
# 1
# 2
