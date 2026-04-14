type StringMap[v] = HashMap[Str, v]

main():
    let m: StringMap[U32] = HashMap.withCapacity(10)
    m.insert("x", 1)
    m.insert("y", 2)
    printStr(m.get("x").toStr())
    printStr(m.get("y").toStr())

# expected stdout:
# Option.Some(1)
# Option.Some(2)
