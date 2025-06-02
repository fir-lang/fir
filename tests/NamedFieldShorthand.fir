type T:
    x: U32
    y: U32
    z: U32

type A:
    A:
        x: U32
        y: U32
        z: U32

main():
    let x = 1u32
    let y = 2u32
    let z = 3u32
    let t = T(z, x, y)
    print("x = `t.x`, y = `t.y`, z = `t.z`")
    let a = A.A(z, x, y)
    match a:
        A.A(x, y, z):
            print("x = `x`, y = `y`, z = `z`")

# expected stdout:
# x = 1, y = 2, z = 3
# x = 1, y = 2, z = 3
