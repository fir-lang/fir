# `type Void` is an empty type. A function that returns it is considered as diverging.
# `type Empty = Empty` is a type with just one term: `Empty`.

type Void

type Empty:
    Empty

returnsEmpty() Empty:
    Empty.Empty

diverges() Void:
     diverges()

expectsEmpty(val: Empty) ():
    ()

test():
    expectsEmpty(diverges())

# args: --typecheck --no-prelude
