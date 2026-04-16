#[NoImplicitPrelude]
import [Fir/Prelude/[Bool as MyBool]]


test() Bool:
    MyBool.True

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/SelectiveImportRenamedFail.fir:5:8: Unbound name Bool
