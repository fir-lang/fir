#[NoImplicitPrelude]
import []

prim type Str
prim type I32

trait T[a]:
    toStr(self: a) Str

impl T[Str]:
    toStr(self: Str) I32:
        123

# args: --typecheck
# expected exit status: 101
# expected stderr:
# Tests/TcFail1.fir:11:5: Trait method implementation of toStr does not match the trait method type
#                                 Trait method type:          [?exn#0: *] Fn(Str) Str / ?exn#0
#                                 Implementation method type: [?exn: *] Fn(Str) I32 / ?exn
