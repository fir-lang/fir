main():
    do:
        do:
            do:
                do:
                    while (foo is Bar.Baz(x, y, z) and blah.blah() and blah is Blah.Blah) or bar is Baz.Qux(x, y, z, t, a, b, c, d):
                        print("hi")

# expected stdout:
# main():
#     do:
#         do:
#             do:
#                 do:
#                     while (foo is Bar.Baz(x, y, z)
#                             and blah.blah()
#                             and blah is Blah.Blah)
#                             or bar is Baz.Qux(x, y, z, t, a, b, c, d):
#                         print("hi")
