main():
    let array: Array[Str] = Array.new(0)
    print("---")
    for i: Str in array.iter():
        printStr(i)
    print("---")

    let array: Array[Str] = Array.new(3)
    array.set(0, "a")
    array.set(1, "b")
    array.set(2, "c")

    for i: Str in array.iter():
        printStr(i)

# expected stdout:
# ---
# ---
# a
# b
# c
