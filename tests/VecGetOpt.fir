main():
    let v: Vec[U32] = Vec.[u32(1), u32(2), u32(3)]
    for i in range(u32(0), 4):
        print(v.getOpt(i))

# expected stdout:
# Option.Some(1)
# Option.Some(2)
# Option.Some(3)
# Option.None
