# Test that return inside a match arm works with value types. This tests that
# the C backend generates proper dummy values for statement expressions
# containing return statements.

type Point:
    Point(x: I32, y: I32)

test(p: Point) I32:
    match p:
        Point.Point(x, y):
            if x == 0:
                return 42
            x + y

main():
    printStr(test(Point.Point(x = 0, y = 10)).toStr())
    printStr(test(Point.Point(x = 3, y = 4)).toStr())

# expected stdout:
# 42
# 7
