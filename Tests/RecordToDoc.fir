main():
    print(().toDoc().render(10))
    print((msg = "Hi").toDoc().render(10))
    print((msg = "Hi").toDoc().render(15))
    print(
        (
            msg = "Hi",
            x = u32(123),
            y = (a = Vec.["a", "b", "c"], b = u32(456)),
            z = (q = u32(0), z = u32(1)),
        ).toDoc().render(15),
    )


# expected stdout:
# ()
# (
#     msg = "Hi",
# )
# (msg = "Hi")
# (
#     msg = "Hi",
#     x = 123,
#     y = (
#         a = Vec.[
#             "a",
#             "b",
#             "c",
#         ],
#         b = 456,
#     ),
#     z = (
#         q = 0,
#         z = 1,
#     ),
# )
