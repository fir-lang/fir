mkRecord() (x: U32, y: U32, z: U32):
    (x = u32(1), y = u32(2), z = u32(3))

main():
    match mkRecord():
        (x, ..rest):
            print(x)
            print(rest.y)
            print(rest.z)

# expected stdout:
# 1
# 2
# 3
