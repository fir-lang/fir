main():
    let x: Vec[U8] = Vec.fromIter(once(1).chain(once(2)).chain(once(3)))
    print(x)
