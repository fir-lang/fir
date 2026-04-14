#[NoImplicitPrelude]
import [Fir/Prelude as P]


test() Bool:
    P/Bool.True


# args: --typecheck
# expected exit status: 101
# expected stderr: tests/PrefixedImportFail.fir:5:8: Unknown type Bool
