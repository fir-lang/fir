type Option[t]:
    None
    Some(t)

prim type U32

main():
    let x: Option[U32] = Option.None
    let y: Option[U32] = Option.None
    match (left = x, right = y):
        (left = Option.Some(i1), right = Option.Some(i2)):
            print("1")
        (left = Option.None, right = Option.None):
            print("2")

# args: --no-prelude --typecheck
