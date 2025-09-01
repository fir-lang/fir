f():
    (x, y, if foo:
               123
           else:
               456)

    x + y + (if foo:
                 123
             else:
                 456) + z

# expected stdout:
# f():
#     (
#         x,
#         y,
#         if foo:
#             123
#         else:
#             456,
#     )
# 
#     x
#         + y
#         + (if foo:
#                123
#            else:
#                456)
#         + z
