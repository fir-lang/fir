trait Test[t]:
    type X
    test(self)

prim type I32

impl Test for I32:
    type X = I32
    type X = Str

    test(self) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/AssocTysFail4.fir:9:5: Associated type X is defined multiple times
