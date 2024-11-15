type T[A: Iterator]:
    iter: A

fn test[A](t: T[A]) = ()

# args: --typecheck --no-backtrace
