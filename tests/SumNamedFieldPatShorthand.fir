type T:
    A:
        x: U32
        y: U32
        z: U32

main
    let val = T.A(x = 123u32, y = 456u32, z = 789u32)

    match val:
        T.A(x, y, z):
            print("x = `x`, y = `y`, z = `z`")

    match val:
        T.A(y, z, x):
            print("x = `x`, y = `y`, z = `z`")

    match val:
        T.A(y = a, z, x = b):
            print("x = `b`, y = `a`, z = `z`")

    match val:
        T.A(y = a, ..):
            print("y = `a`")

    match val:
        T.A(z = x, y = a, ..):
            print("y = `a`, z = `x`")

# expected stdout:
# x = 123, y = 456, z = 789
# x = 123, y = 456, z = 789
# x = 123, y = 456, z = 789
# y = 456
# y = 456, z = 789
