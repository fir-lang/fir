#[NoImplicitPrelude]
import [
    Fir/Prelude/[Bool, U32],
    Fir/Prelude/[Option],
]


test() Result[Option[Bool], U32]:
    Option.None

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/SelectiveImportFail.fir:8:8: Unbound name Result
