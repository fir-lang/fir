main():
    let v: Vec[U32] = Vec.empty()
    print(v.spareCapacity())
    v.reserve(0)
    print(v.spareCapacity())
    v.reserve(10)
    print(v.spareCapacity())
    v.reserve(10)
    print(v.spareCapacity())
    v.reserve(v.spareCapacity())
    print(v.spareCapacity())

# expected stdout:
# 0
# 0
# 16
# 16
# 16
