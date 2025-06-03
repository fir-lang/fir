main():
    let vec: Vec[U32] = Vec.withCapacity(1)
    vec.push(1)

    let doc = vec.iter().map(
        fn(alt: U32) Doc {
            Doc.str("hi")
        })

    let doc = vec.iter().map(
        fn(alt: U32) Doc {
            Doc.str("hi")
        }
    )

    let doc = vec.iter().map(
        fn(alt: U32) Doc {
            Doc.str("hi")
    })

    ()
