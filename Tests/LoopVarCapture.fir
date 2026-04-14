main():
    let funs: Vec[Fn() U32 / []] = Vec.empty()

    for i: U32 in range(u32(0), u32(10)):
        funs.push(\() U32 / []: i)

    for fun: Fn() U32 / [] in funs.iter():
        print(fun())

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
