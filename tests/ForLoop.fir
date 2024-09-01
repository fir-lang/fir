fn fac1(n: I32): I32 =
    let ret = 1
    for i in 2 ..= n:
        ret *= i
    ret

fn fac2(n: I32): I32 =
    let ret = 1
    for i in 2 .. n + 1:
        ret *= i
    ret

fn main(input: Str) =
    printStr(fac1(0).toStr())
    printStr(fac1(5).toStr())
    printStr(fac1(10).toStr())

    printStr(fac2(0).toStr())
    printStr(fac2(5).toStr())
    printStr(fac2(10).toStr())

# expected stdout:
# 1
# 120
# 3628800
# 1
# 120
# 3628800
