prim type U32

type Bool:
    False
    True

type Option[t]:
    Some(t)
    None

f(): Option[(a: U32, b: U32)]
    match Bool.False:
        Bool.True: Option.Some((a = 1, b = 2))
        Bool.False: Option.None

# args: --no-prelude --typecheck
