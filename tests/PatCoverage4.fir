type Option[t]:
    None
    Some(t)


type Bool:
    False
    True


main():
    match (l = Option.None, r = Option.None):
        (l = _, r = _): ()

# args: --no-prelude --typecheck
