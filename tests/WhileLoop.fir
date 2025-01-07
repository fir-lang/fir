fn fac(n: I32): I32
    let ret = 1
    while n != 0:
        ret *= n
        n -= 1
    ret

fn main()
    printStr(fac(0).toStr())
    printStr(fac(5).toStr())
    printStr(fac(10).toStr())

# expected stdout:
# 1
# 120
# 3628800
