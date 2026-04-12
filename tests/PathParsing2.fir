# Test `UpperId / UpperId` parsing, with whitepace before or after `/`.
#
# Without whitespace this becomes a path. With whitespace it's a binary
# expression.
#
# We may want to change this behavior later. This test is to make sure we don't
# change it accidentally.

main():
    print(A / A)
    print(A/ A)
    print(A /A)


type A


impl Div[A]:
    __div(self: A, other: A) A:
        print("A.__div called")
        A


impl ToStr[A]:
    toStr(self: A) Str:
        "A"

# expected stdout:
# A.__div called
# A
# A.__div called
# A
# A.__div called
# A
