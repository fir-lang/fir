main():
    let x: Array[U32] = Array.fromIter([u32(0), u32(1), u32(2)], 3)
    let y = x.slice(1, 3)
    print(x)
    print(y)
    y.set(0, 99)
    x.set(2, 100)
    print(x)
    print(y)

# expected stdout:
# [0,1,2]
# [1,2]
# [0,99,100]
# [99,100]
