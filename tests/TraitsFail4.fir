prim type U32

trait Test[a, b]:
    method(self: a, other: b)

impl Test[U32]:
    method(self: U32, other: b):
        ()

# args: --no-prelude --typecheck --no-backtrace
# expected exit status: 101
# expected stderr: tests/TraitsFail4.fir:6:1: Trait Test takes 2 type arguments, but impl passes 1
