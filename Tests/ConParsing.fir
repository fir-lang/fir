main():
    let x = Option.None[U32]
    let x = Option[U32].None
    let x = Option[U32].None[U32]

    match foo:
        Option.Some(_): ()
        Option[U32].Some(_): ()
        Option.Some[U32](_): ()
        Option[U32].Some[U32](_): ()

        Option.None: ()
        Option[U32].None: ()
        Option.None[U32]: ()
        Option[U32].None[U32]: ()

    match foo:
        Foo(_): ()

    match foo:
        Foo[U32](_): ()

# args: --parse
