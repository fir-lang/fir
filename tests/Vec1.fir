fn main(args: Str) =
    let test = Vec.withCapacity(10)

    for i in 0 .. 20:
        test.push(i)

    for i in 0 .. test.len:
        printStr(test.get(i).toStr())

# expected stdout:
# 0
# 1
# 2
# 3
# 4
# 5
# 6
# 7
# 8
# 9
# 10
# 11
# 12
# 13
# 14
# 15
# 16
# 17
# 18
# 19
