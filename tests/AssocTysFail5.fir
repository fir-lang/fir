trait Test[t]:
    type X
    test(self)

prim type I32

impl Test for I32:
    type X = I32
    type Y = I32
    test(self) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/AssocTysFail5.fir:7:1: Extra associated types defined: {"Y"}
