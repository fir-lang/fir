main():
    let map: HashMap[Str, U32] = HashMap.withCapacity(10)
    printStr(map.insert("a", 1).toStr())
    printStr(map.insert("a", 2).toStr())
    printStr(map.get("a").toStr())
    printStr(map.get("b").toStr())
    printStr(map.toStr())
    printStr(map.insert("b", 3).toStr())
    printStr(map.toStr())

# expected stdout:
# Option.None
# Option.Some(1)
# Option.Some(2)
# Option.None
# {a: 2}
# Option.None
# {b: 3, a: 2}
