main() = expectU32Item(RangeIterator(current = 0u32, end = 10u32))

expectU32Item[i: Iterator[Item = U32]](iter: i) = ()

prim type U32

type Option[t]:
    None
    Some(t)

trait Iterator[t]:
    type Item

    next(self): Option[Item]

type RangeIterator[t]:
    current: t
    end: t

impl[t] Iterator for RangeIterator[t]:
    type Item = t

    next(self): Option[t] = Option.None

# args: --typecheck --no-prelude
