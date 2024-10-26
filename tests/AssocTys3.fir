fn main() = expectU32Item(RangeIterator(current = 0u32, end = 10u32))

fn expectU32Item[I: Iterator[Item = U32]](iter: I) = ()

prim type U32

type Option[T]:
    None
    Some(T)

trait Iterator[T]:
    type Item

    fn next(self): Option[Item]

type RangeIterator[T]:
    current: T
    end: T

impl[T] Iterator for RangeIterator[T]:
    type Item = T

    fn next(self): Option[T] = Option.None

# args: --typecheck --no-prelude
