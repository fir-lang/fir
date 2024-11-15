type T[A: Iterator]:
    iter: A

impl[A] T[A]:
    fn test(self) = ()

# args: --typecheck --no-backtrace
# expected stderr:
# tests/TypeParamBoundsFail2.fir:4:1: Bound Iterator for type parameter A is not in context
