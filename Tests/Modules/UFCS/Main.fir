# With multiple modules importing the same top-level becomes an error at the use
# sites, but with UFCS it's OK as long as only one of them matches the argument
# type.


import [
    Tests/Modules/UFCS/Lib1,
    Tests/Modules/UFCS/Lib2,
]


main():
    Type1(x = 123, msg = "hi").show().print()


# expected stdout:
# Type1(x = 123, msg = hi)
