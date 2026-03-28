type Shape:
    Circle(radius: U32)
    Rect(x: U32, y: U32, w: U32, h: U32)

main():
    let s = Shape.Rect(x = 1, y = 2, w = 10, h = 20)
    let Shape.Rect(x, y, ..rest) = s
    print(x)
    print(y)
    print(rest.w)
    print(rest.h)

# expected stdout:
# 1
# 2
# 10
# 20
