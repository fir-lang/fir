main
    print(Option.None[U32])
    print(foo[[], U32]())
    print(T(x = ()).f[U32, [], Str]())

foo(): Option[t]
    Option.None[t]

type T[a]:
    x: ()

T.f(self: T[a]): Option[t]
    Option.None[t]

# expected stdout:
# Option.None
# Option.None
# Option.None
