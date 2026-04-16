import [
    Tests/Modules/ImplMatching/Lib1 as Lib1,
    Tests/Modules/ImplMatching/Lib2 as Lib2,
]


main():
    print(Lib1/Foo(x = 1, y = 2).toDoc().render(80))
    print(Lib2/Foo(a = 3, b = 4).toDoc().render(80))

# expected stdout:
# Foo(x = 1, y = 2)
# Foo(a = 3, b = 4)
