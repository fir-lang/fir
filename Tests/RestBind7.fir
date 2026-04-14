type Shape:
    Circle(radius: U32)
    Rect(x: U32, y: U32, w: U32, h: U32)

main():
    let s1 = Shape.Circle(radius = 42)
    let s2 = Shape.Rect(x = 1, y = 2, w = 10, h = 20)

    match s1:
        Shape.Circle(radius):
            print(radius)
        Shape.Rect(x, y, ..rest):
            print(rest.w)

    match s2:
        Shape.Circle(radius):
            print(radius)
        Shape.Rect(x, y, ..rest):
            print(x)
            print(y)
            print(rest.w)
            print(rest.h)

# expected stdout:
# 42
# 1
# 2
# 10
# 20
