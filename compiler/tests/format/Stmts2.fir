f():
    for x in range(a, b):
        1

    for x: U32 in range(a, b):
        2

# expected stdout:
# f():
#     for x in range(a, b):
#         1
#     
#     for x: U32 in range(a, b):
#         2
