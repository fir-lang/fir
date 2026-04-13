#[NoImplicitPrelude]
import [Fir/Prelude/[Bool]]

type Type1

test() Type1:
    if Bool.True:
        return Type1

    Type1

# args: --typecheck
