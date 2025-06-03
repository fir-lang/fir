main()
    let (z, x, y) = f()
    print("x = `x`, y = `y`, z = `z`")

    let (x, ..) = f()
    print("x = `x`")

    let (y, ..) = f()
    print("y = `y`")

    let (z, ..) = f()
    print("z = `z`")

    let (x, z, ..) = f()
    print("x = `x`, z = `z`")

    let (z, x, ..) = f()
    print("x = `x`, z = `z`")

f() (x: U32, y: U32, z: U32) = (x = 123u32, y = 456u32, z = 789u32)

# expected stdout:
# x = 123, y = 456, z = 789
# x = 123
# y = 456
# z = 789
# x = 123, z = 789
# x = 123, z = 789
