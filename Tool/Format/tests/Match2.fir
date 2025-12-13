f():
    match f:
        A.B(x) if short(x): 1
        _: 2

    match f:
        A.B(x) if short(x):
            f()
            g()
        _:
            f()
            g()

    match f:
        A.B(x, y, z, t, a, b, c) if longExpression(x, y, z): 1
        _: 2

    match f:
        Longgggggggggggg.Longgggggg(x, y, z, t, a, b, c) if longExpression(x, y, z): 1
        _: 2


f():
    match symbol:
        # Blah blah
        Symbol.Group(symbols): ()

# expected stdout:
# f():
#     match f:
#         A.B(x) if short(x): 1
#         _: 2
# 
#     match f:
#         A.B(x) if short(x):
#             f()
#             g()
#         _:
#             f()
#             g()
# 
#     match f:
#         A.B(x, y, z, t, a, b, c) if longExpression(x, y, z): 1
#         _: 2
# 
#     match f:
#         Longgggggggggggg.Longgggggg(x, y, z, t, a, b, c)
#                 if longExpression(x, y, z):
#             1
#         _: 2
# 
# 
# f():
#     match symbol:
#         # Blah blah
#         Symbol.Group(symbols): ()
