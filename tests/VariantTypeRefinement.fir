type E1:
    E1

type E2:
    E2

type E3:
    E3

f1(args: [E1, E2, E3]) [E2, E3]:
    match args:
        ~E1.E1: ~E2.E2
        ~E2.E2: ~E3.E3
        ~E3.E3: ~E3.E3

f2[VarRow[r]](args: [E1, ..r]) Option[[..r]]:
    match args:
        ~E1.E1: Option.None
        other: Option.Some(other)

main():
    f1(~E1.E1)
    f2(~E2.E2)
    ()
