main():
    let map: HashMap[Str, U32] = HashMap.withCapacity(10)
    printStr(map.toStr())
    printStr(map.insert("a", 1).toStr())
    printStr(map.insert("a", 2).toStr())
    printStr(map.get("a").toStr())
    printStr(map.get("b").toStr())
    printStr(map.toStr())
    printStr(map.insert("b", 3).toStr())
    printStr(map.toStr())

    map.insert("c", 1234)
    map.insert("d", 5678)
    map.insert("e", 9876)
    map.insert("f", 1010)
    map.insert("g", 1212)
    printStr(map.toStr())

# expected stdout:
# {}
# Option.None
# Option.Some(1)
# Option.Some(2)
# Option.None
# {a: 2}
# Option.None
# {b: 3, a: 2}
# {g: 1212, f: 1010, e: 9876, d: 5678, c: 1234, b: 3, a: 2}
