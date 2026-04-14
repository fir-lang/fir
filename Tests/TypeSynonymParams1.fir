type Alias[t] = Vec[t]

main():
    let v: Alias[U32] = Vec.withCapacity(10)
    v.push(1)
    v.push(2)
    v.push(3)
    printStr(v.toStr())

# expected stdout:
# [1,2,3]
