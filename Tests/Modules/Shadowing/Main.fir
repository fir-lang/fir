import [
    Tests/Modules/Shadowing/Lib1,
    Tests/Modules/Shadowing/Lib2 as Lib2,
]


main():
    fun(Foo.A)
    Lib2/fun(Lib2/Foo.A)

# expected stdout:
# Lib1/foo
#   Lib1/Foo.A
# Lib2/fun
#   Lib2/Foo.A
