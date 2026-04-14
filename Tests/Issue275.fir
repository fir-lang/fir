# This program was compiled to ill-typed C because of a substitution bug when
# copying default trait methods.

main():
    let vec: Vec[Str] = Vec.withCapacity(1)
    let iter1 = vec.iter()
    let iter2 = iter1.map(\(s: Str): u32(1))
    let iter3 = iter2.map(\(n: U32): (key = n, val = ()))
