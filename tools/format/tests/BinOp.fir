f():
    do:
        do:
            do:
                do:
                    do:
                        do:
                            do:
                                x is Option.Some(foo) and y is Blah.A and z is a

                                do:
                                    x is Option.Some(foo) and y is Blah.A and z is a

                                    do:
                                        a == 1 or b == 2 or c == 3
                                        a == 1 or b == 2 or c == 3 & 4
                                        a == 1 or b == 2 or c == 3 & 4 & 5
                                        1 & 3 or 4*5 == 6
                                        x is Option.Some(foo) and y is Blah.A and z is a

                                        do:
                                            a == 1 or b == 2 or c == 3
                                            a == 1 or b == 2 or c == 3 & 4
                                            a == 1 or b == 2 or c == 3 & 4 & 5
                                            1 & 3 or 4*5 == 6
                                            x is Option.Some(foo) and y is Blah.A and z is a

                                            do:
                                                a == 1 or b == 2 or c == 3
                                                a == 1 or b == 2 or c == 3 & 4
                                                a == 1 or b == 2 or c == 3 & 4 & 5
                                                1 & 3 or 4*5 == 6
                                                x is Option.Some(foo) and y is Blah.A and z is a

                                                do:
                                                    a == 1 or b == 2 or c == 3
                                                    a == 1 or b == 2 or c == 3 & 4
                                                    a == 1 or b == 2 or c == 3 & 4 & 5
                                                    1 & 3 or 4*5 == 6
                                                    x is Option.Some(foo) and y is Blah.A and z is a

                                                    do:
                                                        a == 1 or b == 2 or c == 3
                                                        a == 1 or b == 2 or c == 3 & 4
                                                        a == 1 or b == 2 or c == 3 & 4 & 5
                                                        1 & 3 or 4*5 == 6
                                                        x is Option.Some(foo) and y is Blah.A and z is a

                                                        do:
                                                            a == 1 or b == 2 or c == 3
                                                            a == 1 or b == 2 or c == 3 & 4
                                                            a == 1 or b == 2 or c == 3 & 4 & 5
                                                            1 & 3 or 4*5 == 6
                                                            x is Option.Some(foo) and y is Blah.A and z is a

                                                            do:
                                                                a == 1 or b == 2 or c == 3
                                                                a == 1 or b == 2 or c == 3 & 4
                                                                a == 1 or b == 2 or c == 3 & 4 & 5
                                                                1 & 3 or 4*5 == 6
                                                                x is Option.Some(foo) and y is Blah.A and z is a

# expected stdout:
# f():
#     do:
#         do:
#             do:
#                 do:
#                     do:
#                         do:
#                             do:
#                                 x is Option.Some(foo) and y is Blah.A and z is a
# 
#                                 do:
#                                     x is Option.Some(foo)
#                                         and y is Blah.A
#                                         and z is a
# 
#                                     do:
#                                         a == 1 or b == 2 or c == 3
#                                         a == 1 or b == 2 or c == 3 & 4
#                                         a == 1 or b == 2 or c == 3 & 4 & 5
#                                         1 & 3 or 4 * 5 == 6
#                                         x is Option.Some(foo)
#                                             and y is Blah.A
#                                             and z is a
# 
#                                         do:
#                                             a == 1 or b == 2 or c == 3
#                                             a == 1 or b == 2 or c == 3 & 4
#                                             a == 1 or b == 2 or c == 3 & 4 & 5
#                                             1 & 3 or 4 * 5 == 6
#                                             x is Option.Some(foo)
#                                                 and y is Blah.A
#                                                 and z is a
# 
#                                             do:
#                                                 a == 1 or b == 2 or c == 3
#                                                 a == 1 or b == 2 or c == 3 & 4
#                                                 a == 1
#                                                     or b == 2
#                                                     or c == 3 & 4 & 5
#                                                 1 & 3 or 4 * 5 == 6
#                                                 x is Option.Some(foo)
#                                                     and y is Blah.A
#                                                     and z is a
# 
#                                                 do:
#                                                     a == 1 or b == 2 or c == 3
#                                                     a == 1
#                                                         or b == 2
#                                                         or c == 3 & 4
#                                                     a == 1
#                                                         or b == 2
#                                                         or c == 3 & 4 & 5
#                                                     1 & 3 or 4 * 5 == 6
#                                                     x is Option.Some(foo)
#                                                         and y is Blah.A
#                                                         and z is a
# 
#                                                     do:
#                                                         a == 1
#                                                             or b == 2
#                                                             or c == 3
#                                                         a == 1
#                                                             or b == 2
#                                                             or c == 3 & 4
#                                                         a == 1
#                                                             or b == 2
#                                                             or c == 3 & 4 & 5
#                                                         1 & 3 or 4 * 5 == 6
#                                                         x is Option.Some(foo)
#                                                             and y is Blah.A
#                                                             and z is a
# 
#                                                         do:
#                                                             a == 1
#                                                                 or b == 2
#                                                                 or c == 3
#                                                             a == 1
#                                                                 or b == 2
#                                                                 or c == 3 & 4
#                                                             a == 1
#                                                                 or b == 2
#                                                                 or c
#                                                                     == 3 & 4 & 5
#                                                             1 & 3 or 4 * 5 == 6
#                                                             x
#                                                                 is Option.Some(
#                                                                     foo
#                                                                 )
#                                                                 and y is Blah.A
#                                                                 and z is a
# 
#                                                             do:
#                                                                 a == 1
#                                                                     or b == 2
#                                                                     or c == 3
#                                                                 a == 1
#                                                                     or b == 2
#                                                                     or c
#                                                                         == 3 & 4
#                                                                 a == 1
#                                                                     or b == 2
#                                                                     or c
#                                                                         == 3 & 4
#                                                                             & 5
#                                                                 1 & 3
#                                                                     or 4 * 5
#                                                                         == 6
#                                                                 x
#                                                                     is Option.Some(
#                                                                         foo
#                                                                     )
#                                                                     and y
#                                                                         is Blah.A
#                                                                     and z is a
