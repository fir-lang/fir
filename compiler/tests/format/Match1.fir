# Below `match` branches should have one empty line in between.

f():
    match x:
        C.A: 1

        C.B:
            2

        C.C: 3

# expected stdout:
# # Below `match` branches should have one empty line in between.
# f():
#     match x:
#         C.A: 1
#         C.B: 2
#         C.C: 3
