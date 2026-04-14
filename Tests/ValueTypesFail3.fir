value type Wrap[t](t)

value type Recursive(Wrap[Recursive])

# args: --typecheck
# expected exit status: 101
# expected stderr: Value type Recursive has infinite size due to recursion
