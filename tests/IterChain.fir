main():
    let iter = once(u32(1)).chain(empty()).chain(once(u32(2))).chain(empty())

    for i: U32 in iter:
        print(i)

    for i: U32 in iter:
        print(i)

    let iter = "abcd".chars().chain(once('e'))

    for i: Char in iter:
        print(i)

    print("---")

    let iter = onceWith(\():
            print("OnceWith 1")
            'a'
        )
        .chain(empty())
        .chain(onceWith(\():
            print("OnceWith 2")
            'b'
        ))
        .chain(empty())

    for i: Char in iter:
        print(i)

    for i: Char in iter:
        print(i)

# expected stdout:
# 1
# 2
# 'a'
# 'b'
# 'c'
# 'd'
# 'e'
# ---
# OnceWith 1
# 'a'
# OnceWith 2
# 'b'
