#[NoImplicitPrelude]
import [
    Fir/Prelude/[Bool, U32],
    Fir/Prelude/[Option],
]


test() Result[Option[Bool], U32]:
    Option.None


# args: --typecheck
# expected exit status: 101
# expected stderr: tests/SelectiveImportFail.fir:8:8: Unknown type Result
