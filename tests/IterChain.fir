main
    let iter = once(1u32).chain(once(2u32))

    for i: U32 in iter:
        print(i)

    for i: U32 in iter:
        print(i)

    let iter = "abcd".chars().chain(once('e'))

    for i: Char in iter:
        print(i)

    print("---")

    let iter = onceWith(fn() {
        print("OnceWith 1")
        'a'
    }).chain(onceWith(fn() {
        print("OnceWith 2")
        'b'
    }))

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
