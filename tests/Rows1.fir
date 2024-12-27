fn test[R](r: (x: I32, y: I32 | R)) = ()

fn main() =
    test((x = 1, y = 2))
