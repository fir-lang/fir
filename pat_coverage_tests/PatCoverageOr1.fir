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

# args: --no-prelude --typecheck
# expected stdout:
# pat_coverage_tests/PatCoverageOr1.fir:16:5: New coverage checker: unexhaustive pattern match

# expected stderr: pat_coverage_tests/PatCoverageOr1.fir:16:5: Unexhaustive pattern match

