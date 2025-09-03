# Below we don't want any empty lines between `x()` and `y()`.

f():
    x() # blah blah
    y()

# expected stdout:
# # Below we don't want any empty lines between `x()` and `y()`.
# 
# f():
#     x() # blah blah
# 
#     y()
