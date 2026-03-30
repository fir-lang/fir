main():
    print(ToDoc.toDoc(()).render(10))
    print(ToDoc.toDoc((msg = "Hi")).render(10))
    print(ToDoc.toDoc((msg = "Hi")).render(15))
    print(
        ToDoc.toDoc(
            (
                msg = "Hi",
                x = u32(123),
                y = (a = Vec.["a", "b", "c"], b = u32(456)),
                z = (q = u32(0), z = u32(1)),
            ),
        ).render(15),
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
