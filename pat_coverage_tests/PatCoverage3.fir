type Option[t]:
    None
    Some(t)

prim type U32

main():
    let x: Option[U32] = Option.None
    let y: Option[U32] = Option.None

    match (left = x, right = y):
        (left = Option.Some(i1), right = Option.Some(i2)): ()
        (left = Option.None, right = Option.None): ()

    match (left = x, right = y):
        (left = Option.Some(i1), right = Option.Some(i2)): ()
        (left = Option.None, right = Option.None): ()
        (left = Option.Some(_), right = Option.None): ()

    match (left = x, right = y):
        (left = Option.Some(i1), right = Option.Some(i2)): ()
        (left = Option.None, right = Option.None): ()
        (left = Option.Some(_), right = Option.None): ()
        (right = Option.Some(_), left = Option.None): ()

    match (left = x, right = y):
        (left = Option.Some(i1), ..): ()

    match (left = x, right = y):
        (right = Option.Some(i1), ..): ()

    match (left = x, right = y):
        (right = Option.Some(..), ..): ()
        (right = Option.None, ..): ()

# args: --no-prelude --typecheck
# expected exit status: 101
# expected stdout:
# pat_coverage_tests/PatCoverage3.fir:11:5: New coverage checker: unexhaustive pattern match
# pat_coverage_tests/PatCoverage3.fir:15:5: New coverage checker: unexhaustive pattern match
# pat_coverage_tests/PatCoverage3.fir:26:5: New coverage checker: unexhaustive pattern match
# pat_coverage_tests/PatCoverage3.fir:29:5: New coverage checker: unexhaustive pattern match

# expected stderr:
# pat_coverage_tests/PatCoverage3.fir:26:5: Unexhaustive pattern match
# pat_coverage_tests/PatCoverage3.fir:29:5: Unexhaustive pattern match
# index out of bounds: the len is 0 but the index is 0

