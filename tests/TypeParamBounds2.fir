type T[A: Iterator]:
    iter: A

impl[A: Iterator] T[A]:
    fn test(self) = ()

fn main() =
    let t = T(iter = "".chars())
    t.test()
    ()
