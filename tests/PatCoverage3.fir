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
# expected stderr:
# tests/PatCoverage3.fir:11:5: Unexhaustive pattern match
# tests/PatCoverage3.fir:15:5: Unexhaustive pattern match
# tests/PatCoverage3.fir:26:5: Unexhaustive pattern match
# tests/PatCoverage3.fir:29:5: Unexhaustive pattern match
