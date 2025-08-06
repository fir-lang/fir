main():
    let vec: Vec[Str] = Vec.[]
    for x: (idx: U32, item: Str) in vec.iter().enumerate():
        print("`x.idx`: `x.item`")

    let vec: Vec[Str] = Vec.["hi", "bye"]
    for x: (idx: U32, item: Str) in vec.iter().enumerate():
        print("`x.idx`: `x.item`")

# expected stdout:
# 0: hi
# 1: bye
