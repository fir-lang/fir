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
        g("world" #| more nesting |#)
    `-")

    print("\`")

f() Str:
    "Hi"

g(s: Str) Str:
    "Hello, `s`!"

# expected stdout:
# Hi
# -Hi-
# -~Hi~-
# -~Hi~Hi~-
# -Hello, world!-
# `
