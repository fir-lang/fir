type T[A: Iterator]:
    iter: A

impl[A] T[A]:
    fn test(self) = ()

# args: --typecheck --no-backtrace
# expected stderr: tests/TypeParamBoundsFail2.fir:4:1: Type T does not implement Iterator
