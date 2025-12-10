type Option[t]:
    None
    Some(t)

main():
    match (l = Option.None, r = Option.None):
        (l = Option.None, r = Option.None): ()
        (l = Option.Some(a), r = Option.Some(b)): ()
        _: ()

# args: --no-prelude --typecheck
