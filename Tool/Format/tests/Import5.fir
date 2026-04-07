import [
    Foo/Bar/*,
    Foo/Bar as Baz,
    Foo/Bar/[a, b, c],
    Foo/Bar/[a as b, c as d],
]

# expected stdout:
# import [
#     Foo/Bar/*,
#     Foo/Bar as Baz,
#     Foo/Bar/[a, b, c],
#     Foo/Bar/[a as b, c as d],
# ]
