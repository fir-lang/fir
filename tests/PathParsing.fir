main():
    let x = A/foo
    let x = A/B         # constructor `B` in `A`
    let x = A/B/foo
    let x = A/B/foo.bar
    let x = A/B/C       # constructor `C` in `A/B`
    let x = A/B.C       # constructor `B.C` in `A`
    let x = A/B/C.D     # constructor `C.D` in `A/B`


# args: --parse
