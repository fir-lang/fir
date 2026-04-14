mkRecord() (x: U32, y: U32, z: U32):
    (x = u32(1), y = u32(2), z = u32(3))

printYZ(r: (y: U32, z: U32)):
    print(r.y)
    print(r.z)

main():
    let (x, ..rest) = mkRecord()
    print(x)
    printYZ(rest)

# expected stdout:
# 1
# 2
# 3
