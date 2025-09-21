main():
    let iter = repeatWith(|| Vec[U32]: Vec.withCapacity(10))
    let vs: Vec[Vec[U32]] = Vec.empty()
    for i in range(u32(0), u32(10)):
        let v: Vec[U32] = iter.next().unwrap()
        v.push(i)
        vs.push(v)
    print(vs)

# expected stdout: [[0],[1],[2],[3],[4],[5],[6],[7],[8],[9]]
