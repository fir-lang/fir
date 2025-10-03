# Output of this program depends on hashing. Ideally we should be able to test
# this as a unit test, but until we have the features and infra to do that, we
# should check that capacities left below are: 0 (length 0), 7 (length 10), and
# 12 (length 40, with 20 elements). Just update the test expectations as long as
# these are correct.
main():
    let map = HashMap[U32, U32].withCapacity(0)
    print(map.toDebugDoc().render(80))

    map.insert(0, 0)
    print(map.toDebugDoc().render(80))

    for i: U32 in range(u32(1), u32(20)):
        map.insert(i, i)
    print(map.toDebugDoc().render(80))


# expected stdout:
# HashMap(_elems = Array.[], _capacityLeft = 0)
# HashMap(
#     _elems =
#         Array.[
#             Option.Some(Elem(key = 0, value = 0, next = Option.None)),
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None
#         ],
#     _capacityLeft = 7
# )
# HashMap(
#     _elems =
#         Array.[
#             Option.Some(Elem(key = 0, value = 0, next = Option.None)),
#             Option.Some(Elem(key = 1, value = 1, next = Option.None)),
#             Option.Some(Elem(key = 2, value = 2, next = Option.None)),
#             Option.Some(Elem(key = 3, value = 3, next = Option.None)),
#             Option.Some(Elem(key = 4, value = 4, next = Option.None)),
#             Option.Some(Elem(key = 5, value = 5, next = Option.None)),
#             Option.Some(Elem(key = 6, value = 6, next = Option.None)),
#             Option.Some(Elem(key = 7, value = 7, next = Option.None)),
#             Option.Some(Elem(key = 8, value = 8, next = Option.None)),
#             Option.Some(Elem(key = 9, value = 9, next = Option.None)),
#             Option.Some(Elem(key = 10, value = 10, next = Option.None)),
#             Option.Some(Elem(key = 11, value = 11, next = Option.None)),
#             Option.Some(Elem(key = 12, value = 12, next = Option.None)),
#             Option.Some(Elem(key = 13, value = 13, next = Option.None)),
#             Option.Some(Elem(key = 14, value = 14, next = Option.None)),
#             Option.Some(Elem(key = 15, value = 15, next = Option.None)),
#             Option.Some(Elem(key = 16, value = 16, next = Option.None)),
#             Option.Some(Elem(key = 17, value = 17, next = Option.None)),
#             Option.Some(Elem(key = 18, value = 18, next = Option.None)),
#             Option.Some(Elem(key = 19, value = 19, next = Option.None)),
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None,
#             Option.None
#         ],
#     _capacityLeft = 12
# )
