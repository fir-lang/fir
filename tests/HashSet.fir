main():
    let set: HashSet[Str] = HashSet.withCapacity(10)
    print(set.insert("a"))
    print(set.insert("b"))
    print(set.insert("c"))
    print(set.insert("d"))
    print(set.toDoc().render(80))
    print(set.contains("a"))
    print(set.contains("b"))
    print(set.contains("c"))
    print(set.contains("d"))

# expected stdout:
# Bool.True
# Bool.True
# Bool.True
# Bool.True
# {"d", "c", "b", "a"}
# Bool.True
# Bool.True
# Bool.True
# Bool.True
