type Iter:
    next: U32

impl Iterator[Iter, U32, errs]:
    next(self: Iter): [..errs] Option[U32]
        if self.next == 3:
            printStr("Stopping")
            Option.None
        else:
            printStr("Generating next item: `self.next.toStr()`")
            let next = self.next
            self.next += 1
            Option.Some(next)

main
    let iter = Iter(next = 0)
    let peekable: Peekable[Iter, U32] = iter.peekable()
    let next: Option[U32] = peekable.next()
    printStr(next.toStr())
    let next: Option[U32] = peekable.peek()
    printStr(next.toStr())
    let next: Option[U32] = peekable.peek()
    printStr(next.toStr())
    let next: Option[U32] = peekable.next()
    printStr(next.toStr())
    let next: Option[U32] = peekable.next()
    printStr(next.toStr())
    let next: Option[U32] = peekable.peek()
    printStr(next.toStr())
    let next: Option[U32] = peekable.next()
    printStr(next.toStr())
    ()

# expected stdout:
# Generating next item: 0
# Option.Some(0)
# Generating next item: 1
# Option.Some(1)
# Option.Some(1)
# Option.Some(1)
# Generating next item: 2
# Option.Some(2)
# Stopping
# Option.None
# Stopping
# Option.None
