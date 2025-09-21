main():
    let vec: Vec[U32] = [u32(0), u32(1), u32(3)]
    print(vec.iter().find(|i: U32| Bool: i == 0))
    print(vec.iter().find(|i: U32| Bool: i == 2))
    print(vec.iter().find(|i: U32| Bool: i == 3))

# expected stdout:
# Option.Some(0)
# Option.None
# Option.Some(3)
