# `type Void` is an empty type. A function that returns it is considered as diverging.
# `type Empty = Empty` is a type with just one term: `Empty`.

type Void

type Empty:
    Empty

fn returnsEmpty(): Empty
    Empty.Empty

fn diverges(): Void
     diverges()

fn expectsEmpty(value: Empty): ()
    ()

fn test()
    expectsEmpty(diverges())

# args: --typecheck --no-prelude
