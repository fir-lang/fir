type Option[t]:
    None
    Some(t)


main():
    match (l = Option.None, r = Option.None):
        _: ()

    match (l = (l = Option.None, r = Option.None), r = Option.None):
        (l = _, r = _): ()

    match (l = (l = Option.None, r = Option.None), r = Option.None):
        (l = _, ..): ()

# args: --no-prelude --typecheck
