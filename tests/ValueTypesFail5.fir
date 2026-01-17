value type Point(
    x: U32,
    y: U32,
)

main():
    let p = Point(x = 1, y = 2)
    p.x += 1

# expected exit status: 101
# expected stderr: tests/ValueTypesFail5.fir:8:5: Value types can't be updated
