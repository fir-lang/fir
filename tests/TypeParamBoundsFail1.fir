type T[A: Iterator]:
    iter: A

fn main() =
    let t = T(iter = 123i32)
    ()

# args: --typecheck --no-backtrace
# expected stderr: tests/TypeParamBoundsFail1.fir:5:13: Type I32 does not implement trait Iterator
