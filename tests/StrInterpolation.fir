main():
    print("Hi")
    print("-`f()`-")
    print("-`"~`f()`~"`-")
    print("-`"~`f()`~`f()`~"`-")
    print("-`do:
        f()
    `-")

f() Str:
    "Hi"

# expected stdout:
# Hi
# -Hi-
# -~Hi~-
# -~Hi~Hi~-
# -Hi-
