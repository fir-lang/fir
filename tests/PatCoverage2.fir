type Option[t]:
    None
    Some(t)

type Bool:
    False
    True

f() Option[Bool]:
    Option.Some(Bool.True)

main():
    match f():
        Option.None: ()

    match f():
        Option.Some(_): ()

    match f():
        Option.None: ()

    match f():
        Option.None: ()
        Option.Some(_): ()

    match f():
        Option.Some(_): ()
        Option.None: ()

    match f():
        Option.Some(Bool.True): ()
        Option.None: ()

    match f():
        Option.Some(Bool.False): ()
        Option.None: ()

    match f():
        Option.Some(Bool.False): ()
        Option.Some(Bool.True): ()
        Option.None: ()

    match f():
        Option.Some(Bool.True): ()
        Option.None: ()
        Option.Some(Bool.False): ()

# args: --no-prelude --typecheck
# expected stderr:
# tests/PatCoverage2.fir:13:5: Unexhaustive pattern match
# tests/PatCoverage2.fir:16:5: Unexhaustive pattern match
# tests/PatCoverage2.fir:19:5: Unexhaustive pattern match
# tests/PatCoverage2.fir:30:5: Unexhaustive pattern match
# tests/PatCoverage2.fir:34:5: Unexhaustive pattern match
