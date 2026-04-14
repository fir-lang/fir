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
# HashMap(_buckets = Array.[], _capacityLeft = 0, _numElements = 0)
# HashMap(
#     _buckets =
#         Array.[
#             Option.Some(Elem(key = 0, val = 0, next = Option.None)),
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
#     _capacityLeft = 7,
#     _numElements = 1
# )
# HashMap(
#     _buckets =
#         Array.[
#             Option.Some(Elem(key = 0, val = 0, next = Option.None)),
#             Option.Some(Elem(key = 1, val = 1, next = Option.None)),
#             Option.Some(Elem(key = 2, val = 2, next = Option.None)),
#             Option.Some(Elem(key = 3, val = 3, next = Option.None)),
#             Option.Some(Elem(key = 4, val = 4, next = Option.None)),
#             Option.Some(Elem(key = 5, val = 5, next = Option.None)),
#             Option.Some(Elem(key = 6, val = 6, next = Option.None)),
#             Option.Some(Elem(key = 7, val = 7, next = Option.None)),
#             Option.Some(Elem(key = 8, val = 8, next = Option.None)),
#             Option.Some(Elem(key = 9, val = 9, next = Option.None)),
#             Option.Some(Elem(key = 10, val = 10, next = Option.None)),
#             Option.Some(Elem(key = 11, val = 11, next = Option.None)),
#             Option.Some(Elem(key = 12, val = 12, next = Option.None)),
#             Option.Some(Elem(key = 13, val = 13, next = Option.None)),
#             Option.Some(Elem(key = 14, val = 14, next = Option.None)),
#             Option.Some(Elem(key = 15, val = 15, next = Option.None)),
#             Option.Some(Elem(key = 16, val = 16, next = Option.None)),
#             Option.Some(Elem(key = 17, val = 17, next = Option.None)),
#             Option.Some(Elem(key = 18, val = 18, next = Option.None)),
#             Option.Some(Elem(key = 19, val = 19, next = Option.None)),
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
#     _capacityLeft = 12,
#     _numElements = 20
# )
