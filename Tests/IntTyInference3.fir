main():
    let x: Vec[U8] = Vec.fromIter(once(0).chain(once(255)))
    print(x)


# expected stdout: [0,255]
