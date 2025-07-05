trait Trait1[a]:
    t1(self: a)

trait Trait2[a]:
    t2(self: a)

type Type[x]:
    x: x

impl Trait1[Type[x]]:
    t1[Trait2[x]](self: Type[x])
        ()

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/Issue142.fir:11:5: Trait method implementation of t1 does not match the trait method type
#                                 Trait method type:          [?exn#0: *] Fn(Type[x]) ?exn#0 ()
#                                 Implementation method type: [?exn: *] [Trait2[x]] Fn(Type[x]) ?exn ()
#
