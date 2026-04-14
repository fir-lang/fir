type StringVec = Vec[Str]

main():
    let v: StringVec = Vec.withCapacity(10)
    v.push("hello")
    v.push("world")
    printStr(v.toStr())

# expected stdout:
# [hello,world]
