main():
    let f1 = \(x: U32) U32: x
    let f2 = \(x: U32, y: U32) U32: x + y
    print(f1(123))
    print(f2(123, 456))

# expected stdout:
# 123
# 579
