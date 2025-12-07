#|
This example used to loop. When we have a matrix like:

      [ [ _, ... ] ]

We check all constructors or `Recursive`. When checking a constructor against a
wildcard pattern like `_` or a variable, we then expand the `_` as:

      [ [ Recursive.A,    ... ]
        [ Recursive.B(_), ... ] ]

We then check the constructor `A` which is covered. When checking `B` though, we
filter the rows as usual and get:

      [ [ _, ... ] ]

Which takes us to the original matrix, so we loop.

The reason for this is to handle cases like:

    match x:
        (Recursive.A, p1): ...
        (Recursive.B(Recursive.A), p2): ...
        (_, p3): ...

Here when checking `A`, we want the matrix:

      [ [ p1 ]
        [ p3 ] ]

And when checking `B`, we want:

      [ [ Recursive.A, p2 ]
        [ _,           p3 ] ]

But the second row causes looping.
|#

type Recursive:
    A
    B(Recursive)


main():
    match Recursive.A:
        _: ()

# args: --no-prelude --typecheck
