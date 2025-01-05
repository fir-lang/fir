trait Test[t]:
    type X
    fn test(self)

prim type I32

impl Test for I32:
    fn test(self) = ()

# args: --typecheck --no-prelude --no-backtrace
# expected stderr: tests/AssocTysFail3.fir:7:1: Missing associated types: {"X"}
