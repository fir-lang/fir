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
# pat_coverage_tests/PatCoverage1.fir:6:5: New coverage checker: unexhaustive pattern match
# pat_coverage_tests/PatCoverage1.fir:9:5: New coverage checker: unexhaustive pattern match

# expected stderr:
# pat_coverage_tests/PatCoverage1.fir:6:5: Unexhaustive pattern match
# pat_coverage_tests/PatCoverage1.fir:9:5: Unexhaustive pattern match
