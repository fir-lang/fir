expectUnit(unit: ()):
    ()

main():
    let (..r) = ()
    expectUnit(r)

    let (x, ..r) = (x = "hi")
    expectUnit(r)

    match ():
        (..r): expectUnit(r)

    match (x = "hi"):
        (x, ..r): expectUnit(r)
