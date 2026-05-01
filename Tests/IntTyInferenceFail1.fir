main():
    let x: Vec[U8] = Vec.fromIter(once(1).chain(once(2)).chain(once(256)))
    print(x)


# expected exit status: 101
# expected stderr: Tests/IntTyInferenceFail1.fir:2:69: Integer literal 256 out of range for U8
