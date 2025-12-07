#|
This example used to loop. When we have a matrix like:

      [ [ Recursive:_, ...] ]

We check all constructors or `Recrusive`. When checking a constructor against a
wildcard pattern like `_` or a variable, we then expand it to

      [ [ Recursive:Recursive.A,    ...]
        [ Recursive:Recursive.B(_), ...] ]

We then check the constructor `A` which is covered. When checking `B` though, we
focus filter the rows as usual and get:

      [ [ Recursive:_, ... ] ]

Which takes us to the original matrix, so we loop.
|#

type Recursive:
    A
    B(Recursive)


main():
    match Recursive.A:
        _: ()

# args: --no-prelude --typecheck
