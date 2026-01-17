value type T1(T2)

value type T2(T1)

# args: --typecheck
# expected exit status: 101
# expected stderr: Value type T1 has infinite size due to recursion
