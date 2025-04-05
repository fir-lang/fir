main
    'outer: for i: I32 in range(0, 4):
        'inner: for j: I32 in range(0, 4):
            if j & 0b1 == 0b1:
                continue 'inner
            if i & 0b1 == 0b1:
                continue 'outer
            printStr("i = `i.toStr()`, j = `j.toStr()`")

# expected stdout:
# i = 0, j = 0
# i = 0, j = 2
# i = 2, j = 0
# i = 2, j = 2
