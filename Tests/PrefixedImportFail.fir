#[NoImplicitPrelude]
import [Fir/Prelude as P]


test() Bool:
    P/Bool.True

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/PrefixedImportFail.fir:5:8: Unknown type Bool
