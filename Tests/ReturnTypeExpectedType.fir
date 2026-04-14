#[NoImplicitPrelude]
import []

type Type1

type Bool:
    False
    True

type Option[t]:
    Some(t)
    None

f() Option[(a: Type1, b: Type1)]:
    match Bool.False:
        Bool.True: Option.Some((a = Type1, b = Type1))
        Bool.False: Option.None

# args: --typecheck
