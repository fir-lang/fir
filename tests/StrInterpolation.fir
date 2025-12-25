main():
    print("Hi")
    print("-`f()`-")
    print("-`"~`f()`~"`-")
    print("-`"~`f()`~`f()`~"`-")
    print("-`do:
        # Comment 1
            #| Comment 2 |#
                #| Nested #| Comment #| 3
        |#
    |#
|#
        f()
    `-")

    print("\`")

f() Str:
    "Hi"

# expected stdout:
# Hi
# -Hi-
# -~Hi~-
# -~Hi~Hi~-
# -Hi-
# `
