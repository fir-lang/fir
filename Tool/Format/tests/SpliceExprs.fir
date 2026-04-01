main():
    let x = (..rest)
    let x = (msg = "hello", number = u32(123456), ..rest)
    do:
        do:
            do:
                do:
                    do:
                        do:
                            do: 
                                do: 
                                    let x = (msg = "hello", number = u32(123456), ..rest)
                            let x = (msg = "hello", number = u32(123456), ..rest)

    foo(..rest)
    fooooooooooooo(msg = "hello", number = u32(123456), ..rest)
    do:
        do:
            do:
                do:
                    do:
                        do:
                            do:
                                foooooooooooooo(msg = "helloooooo", number = u32(123456), ..rest)
                    fooooooooooooooo(msg = "hello", number = u32(123456), ..rest)

# expected stdout:
# main():
#     let x = (..rest)
#     let x = (msg = "hello", number = u32(123456), ..rest)
#     do:
#         do:
#             do:
#                 do:
#                     do:
#                         do:
#                             do:
#                                 do:
#                                     let x = (
#                                         msg = "hello",
#                                         number = u32(123456),
#                                         ..rest
#                                     )
#                             let x = (
#                                 msg = "hello", number = u32(123456), ..rest
#                             )
# 
#     foo(..rest)
#     fooooooooooooo(msg = "hello", number = u32(123456), ..rest)
#     do:
#         do:
#             do:
#                 do:
#                     do:
#                         do:
#                             do:
#                                 foooooooooooooo(
#                                     msg = "helloooooo",
#                                     number = u32(123456),
#                                     ..rest
#                                 )
#                     fooooooooooooooo(
#                         msg = "hello", number = u32(123456), ..rest
#                     )
