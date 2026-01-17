# This test will be updated to use the types when we implement value types in
# the backends.

value type MyBool:
    True
    False

value type MyChar(_codePoint: U32)

# args: --typecheck
