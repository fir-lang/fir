#[NoImplicitPrelude]
import [Fir/Prelude as P]


test() P/Option[P/Bool]:
    P/Option.Some(P/Bool.True)


# args: --typecheck
