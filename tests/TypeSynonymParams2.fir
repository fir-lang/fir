type B[t] = A[t]

type A[t] = Vec[t]

main():
    let v: B[U32] = Vec.withCapacity(10)
    v.push(42)
    printStr(v.toStr())

# expected stdout:
# [42]

