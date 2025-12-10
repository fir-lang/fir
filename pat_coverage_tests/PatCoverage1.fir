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

# args: --no-prelude --typecheck
# expected stderr:
# pat_coverage_tests/PatCoverage1.fir:6:5: Unexhaustive pattern match
# pat_coverage_tests/PatCoverage1.fir:9:5: Unexhaustive pattern match
