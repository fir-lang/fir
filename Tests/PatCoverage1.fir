#[NoImplicitPrelude]
import []

type Bool:
    False
    True

main():
    match Bool.True:
        Bool.True: ()

    match Bool.True:
        Bool.False: ()

    match Bool.True:
        _: ()

    match Bool.True:
        a: ()

    match Bool.True:
        Bool.True: ()
        Bool.False: ()

    match Bool.True:
        Bool.False: ()
        Bool.True: ()

# args: --typecheck
# expected stderr:
# Tests/PatCoverage1.fir:9:5: Unexhaustive pattern match
# Tests/PatCoverage1.fir:12:5: Unexhaustive pattern match
