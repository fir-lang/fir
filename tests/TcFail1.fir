prim type Str
prim type I32

trait T[a]:
    toStr(self: a): Str

impl T[Str]:
    toStr(self: Str): I32
        123

# args: --typecheck --no-prelude --no-backtrace
# expected exit status: 101
# expected stderr:
# tests/TcFail1.fir:8:5: Trait method implementation of toStr does not match the trait method type
#                                 Trait method type:          [?exn: row(variant)] Fn(Str): [..?exn] Str
#                                 Implementation method type: [?exn: row(variant)] Fn(Str): [..?exn] I32
