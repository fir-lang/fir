main():
    let array: Array[Str] = Array.fromIter([], 0)
    print(" 0: `array`")

    array.reverse()
    print(" 1: `array`")

    array = Array.fromIter(["a"], 1)
    print(" 2: `array`")

    array.reverse()
    print(" 3: `array`")

    array = Array.fromIter(["-", "a", "b", "c", "-"], 5)
    print(" 4: `array`")

    array.reverse()
    print(" 5: `array`")

    array.reverseRange(1, 4)
    print(" 6: `array`")

    array.reverseRange(1, 3)
    print(" 7: `array`")

    array.reverseRange(1, 2)
    print(" 8: `array`")

    array.reverseRange(1, 1)
    print(" 9: `array`")

    array.reverseRange(1, 0)
    print("10: `array`")

# expected stdout:
#  0: []
#  1: []
#  2: [a]
#  3: [a]
#  4: [-,a,b,c,-]
#  5: [-,c,b,a,-]
#  6: [-,a,b,c,-]
#  7: [-,b,a,c,-]
#  8: [-,b,a,c,-]
#  9: [-,b,a,c,-]
# 10: [-,b,a,c,-]
