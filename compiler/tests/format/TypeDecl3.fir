type A:
    A1
    A2

type A:
    # blah blah
    A1
    A2

type A:
    A1
    # blah blah
    A2

type A:
    A1

    A2

type A:
    # blah blah
    A1

    # blah blah
    A2

# expected stdout:
# type A:
#     A1
#     A2
# 
# 
# type A:
#     # blah blah
#     A1
#     A2
# 
# 
# type A:
#     A1
#     
#     # blah blah
#     A2
# 
# 
# type A:
#     A1
#     
#     A2
# 
# 
# type A:
#     # blah blah
#     A1
#     
#     # blah blah
#     A2
