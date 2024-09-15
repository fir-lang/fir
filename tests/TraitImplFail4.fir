prim type I32

trait T[A]:
    fn a(self)

impl T[I32]:
    fn a(self): I32 = 123

# args: --typecheck --no-prelude --no-backtrace
# expected stderr:
# tests/TraitImplFail4.fir:7:5: Trait method implementation of a does not match the trait method type
#                                 Trait method type:          Fn(I32): ()
#                                 Implementation method type: Fn(I32): I32
