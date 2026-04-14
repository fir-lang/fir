test(r: (x: I32, y: I32, ..r)):
    printStr(r.x.toStr())
    printStr(r.y.toStr())

main():
    test((x = 123))

# args: --typecheck
# expected exit status: 101
# expected stderr: Tests/RowsFail1.fir:6:10: Unable to unify (x: I32) with (x: I32, y: I32, .._0)
