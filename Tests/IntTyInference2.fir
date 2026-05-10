main():
    let x = 1
    let y = 2
    print(x + y)
    f(x)


f(x: U64):
    print("in f")

# expected stdout:
# 3
# in f
