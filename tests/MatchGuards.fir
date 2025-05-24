main
    let x: Option[U32] = Option.Some(120)
    match x:
        Option.Some(i) if i.mod(2) == 0: print(i)
        _: panic("WAT")

    # Check exhaustiveness.
    match x:
        Option.Some(i) if i.mod(2) == 0: print(i)
        Option.None: panic("WAT")

    # Check `is` scoping.
    # Currently broken, see #122.
    # let y: Option[Option[U32]] = Option.Some(Option.Some(123))
    # match y:
    #     Option.Some(y) if y is Option.Some(y): print(y)
    #     _: panic("WAT")
    # print(y)

    # Check `is` scoping.
    let z: Option[Option[U32]] = Option.Some(Option.Some(123))
    match z:
        Option.Some(q1) if q1 is Option.Some(q2):
            print(q1)
            print(q2)
        _: panic("WAT")

# expected stdout:
# tests/MatchGuards.fir:8:5: Unexhaustive pattern match
# 120
# 120
# Option.Some(123)
# 123
