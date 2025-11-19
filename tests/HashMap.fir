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
# Option.None
