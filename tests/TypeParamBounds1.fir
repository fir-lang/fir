type T[A: Iterator]:
    iter: A

fn main() =
    let t = T(iter = "".chars())
    ()
