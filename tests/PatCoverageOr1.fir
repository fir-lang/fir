#[NoImplicitPrelude]
import []

type Bool:
    False
    True

type Option[t]:
    None
    Some(t)

main():
    match Bool.True:
        Bool.True | Bool.False: ()

    match Option.None:
        Option.Some(_) | Option.None: ()

    match Option.None:
        Option.Some(Bool.True) | Option.None: ()

    match Option.None:
        Option.Some(Bool.True | Bool.False) | Option.None: ()

# args: --typecheck
# expected stderr: tests/PatCoverageOr1.fir:19:5: Unexhaustive pattern match
