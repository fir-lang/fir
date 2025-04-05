prim type I32

trait T[a]:
    a(self: a)

impl T[I32]:
    a(self: I32): I32 = 123

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/TraitImplFail4.fir:7:5: Trait method implementation of a does not match the trait method type
#                                 Trait method type:          [?exn: row(variant)] Fn(I32): [..?exn] ()
#                                 Implementation method type: [?exn: row(variant)] Fn(I32): [..?exn] I32
