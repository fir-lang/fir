f():
    (x, y, if foo:
               123
           else:
               456)

    # It would be good to align `if` and `else` below, but that's going to be a lot of code for a
    # rare case. We can't just align all the time as that would break the next example below.
    x + y + (if foo:
                 123
             else:
                 456) + z

    let foo = if blah:
        123
    else:
        456

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
#     # It would be good to align `if` and `else` below, but that's going to be a lot of code for a
#     # rare case. We can't just align all the time as that would break the next example below.
#     x
#         + y
#         + (if foo:
#             123
#         else:
#             456)
#         + z
# 
#     let foo = if blah:
#         123
#     else:
#         456
