main():
    let x = (a = "hi", b = match f():
                Option.Some(a): a
                Option.None: 'a', c = u32(1))

    print(x.a)
    print(x.b)
    print(x.c)

f() Option[Char]:
    Option.None

# expected stdout:
# hi
# 'a'
# 1
