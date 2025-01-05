fn f1(args: [E1, E2, E3]): [E2, E3] =
    match args:
        `E1: `E2
        `E2: `E3
        `E3: `E3

fn f2[r](args: [E1, ..r]): Option[[..r]] =
    match args:
        `E1: Option.None
        other: Option.Some(other)

fn main() =
    f1(`E1)
    f2(`E2)
    ()
