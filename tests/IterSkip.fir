type MyIter:
    start: U32
    end: U32

impl Iterator[MyIter, U32, exn]:
    next(self: MyIter): exn Option[U32]
        print("next")
        let next = self.start
        if next == self.end:
            Option.None
        else:
            self.start += 1
            Option.Some(next)

main
    print("----- 1")
    for x: U32 in MyIter(start = 0, end = 5).skip(0):
        print(x)

    print("----- 2")
    for x: U32 in MyIter(start = 0, end = 5).skip(3):
        print(x)

    print("----- 3")
    for x: U32 in MyIter(start = 0, end = 5).skip(5):
        print(x)

    # `Skip` could stop calling `next` after the first `None`, but it's probably also fine to just
    # call it.
    print("----- 4")
    for x: U32 in MyIter(start = 0, end = 0).skip(5):
        print(x)

# expected stdout:
# ----- 1
# next
# 0
# next
# 1
# next
# 2
# next
# 3
# next
# 4
# next
# ----- 2
# next
# next
# next
# next
# 3
# next
# 4
# next
# ----- 3
# next
# next
# next
# next
# next
# next
# ----- 4
# next
# next
# next
# next
# next
# next
