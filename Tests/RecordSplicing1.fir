f() (x: U32, y: U32):
    (x = 1, y = 2)

main():
    let x = (msg = "hi", ..f())
    print(x.msg)
    print(x.x)
    print(x.y)

# expected stdout:
# hi
# 1
# 2
