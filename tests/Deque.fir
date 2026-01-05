main():
    let d: Deque[U32] = Deque.empty()
    print("front = `d.popFront()`")
    print("back = `d.popBack()`")
    p(d)

    d.pushBack(1)
    p(d)

    d.pushBack(2)
    p(d)

    d.pushFront(0)
    p(d)

    print(d.popFront())
    p(d)
    print(d.popBack())
    p(d)
    print(d.popFront())
    p(d)

    d = Deque.empty()
    for i in range(u32(0), 10):
        d.pushFront(i)
    for i in range(u32(0), 10):
        if d.popBack().unwrap() != i:
            panic("pushFront or popBack bug")
    if d.len() != 0:
        panic("pushBack or popFront bug")

    d = Deque.empty()
    for i in range(u32(0), 10):
        d.pushBack(i)
    for i in range(u32(0), 10):
        if d.popFront().unwrap() != i:
            panic("pushBack or popFront bug")
    if d.len() != 0:
        panic("pushBack or popFront bug")


p(d: Deque[U32]):
    print("`d` (len = `d.len()`)")

# expected stdout:
# front = Option.None
# back = Option.None
# [] (len = 0)
# [1] (len = 1)
# [1,2] (len = 2)
# [0,1,2] (len = 3)
# Option.Some(0)
# [1,2] (len = 2)
# Option.Some(2)
# [1] (len = 1)
# Option.Some(1)
# [] (len = 0)
