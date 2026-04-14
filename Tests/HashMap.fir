main():
    let map: HashMap[Str, U32] = HashMap.withCapacity(10)
    printStr(map.toStr())
    printStr(map.toDoc().render(80))
    printStr(map.insert("a", 1).toStr())
    printStr(map.insert("a", 2).toStr())
    printStr(map.get("a").toStr())
    printStr(map.get("b").toStr())
    printStr(map.toStr())
    printStr(map.toDoc().render(80))
    printStr(map.insert("b", 3).toStr())
    printStr(map.toStr())
    printStr(map.toDoc().render(80))

    map.insert("c", 1234)
    printStr(map.toDoc().render(80))
    map.insert("d", 5678)
    printStr(map.toDoc().render(80))
    map.insert("e", 9876)
    printStr(map.toDoc().render(80))
    map.insert("f", 1010)
    printStr(map.toDoc().render(80))
    map.insert("g", 1212)
    printStr(map.toDoc().render(80))
    map.insert("h", 9898)
    printStr(map.toDoc().render(80))

    print(map.remove("d"))
    print(map.remove("d"))
    print(map.remove("f"))
    print(map.remove("f"))
    print(map.remove("h"))
    print(map.remove("h"))
    print(map.remove("g"))
    print(map.remove("g"))
    print(map.remove("a"))
    print(map.remove("a"))
    print(map.remove("b"))
    print(map.remove("b"))
    print(map.remove("c"))
    print(map.remove("c"))
    print(map.remove("e"))
    print(map.remove("e"))
    printStr(map.toDoc().render(80))

    map = HashMap.empty()
    print(map.get("hi"))

# expected stdout:
# {}
# HashMap.[]
# Option.None
# Option.Some(1)
# Option.Some(2)
# Option.None
# {a: 2}
# HashMap.["a" = 2]
# Option.None
# {b: 3, a: 2}
# HashMap.["b" = 3, "a" = 2]
# HashMap.["c" = 1234, "b" = 3, "a" = 2]
# HashMap.["d" = 5678, "c" = 1234, "b" = 3, "a" = 2]
# HashMap.["e" = 9876, "d" = 5678, "c" = 1234, "b" = 3, "a" = 2]
# HashMap.["f" = 1010, "e" = 9876, "d" = 5678, "c" = 1234, "b" = 3, "a" = 2]
# HashMap.[
#     "g" = 1212,
#     "f" = 1010,
#     "e" = 9876,
#     "d" = 5678,
#     "c" = 1234,
#     "b" = 3,
#     "a" = 2,
# ]
# HashMap.[
#     "g" = 1212,
#     "f" = 1010,
#     "e" = 9876,
#     "d" = 5678,
#     "c" = 1234,
#     "b" = 3,
#     "a" = 2,
#     "h" = 9898,
# ]
# Option.Some(5678)
# Option.None
# Option.Some(1010)
# Option.None
# Option.Some(9898)
# Option.None
# Option.Some(1212)
# Option.None
# Option.Some(2)
# Option.None
# Option.Some(3)
# Option.None
# Option.Some(1234)
# Option.None
# Option.Some(9876)
# Option.None
# HashMap.[]
# Option.None
