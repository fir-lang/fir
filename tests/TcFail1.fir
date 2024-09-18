prim type Str
prim type I32

trait T[A]:
    fn toStr(self): Str

impl T for Str:
    fn toStr(self): I32 =
        123

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/TcFail1.fir:8:5: Trait method implementation of toStr does not match the trait method type
#                                 Trait method type:          Fn(Str): Str
#                                 Implementation method type: Fn(Str): I32
