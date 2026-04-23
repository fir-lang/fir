#[NoImplicitPrelude]
import [
    Tests/Modules/SynonymCons/Lib,
    Tests/Modules/SynonymCons/Lib as Lib,
]


type T2 = T1


type T3 = Lib/T1


f1() T1: T1.A
f2() T1: T2.A
f3() T1: T3.A
f4() T2: T1.A
f5() T2: T2.A
f6() T2: T3.A
f7() T3: T1.A
f8() T3: T2.A
f9() T3: T3.A


f10():
    match f1():
        T1.A: ()
        T1.B: ()


f11():
    match f1():
        T2.A: ()
        T2.B: ()


f13():
    match f1():
        T3.A: ()
        T3.B: ()


f14():
    match f4():
        T1.A: ()
        T1.B: ()


f15():
    match f4():
        T2.A: ()
        T2.B: ()


f16():
    match f4():
        T3.A: ()
        T3.B: ()


f17():
    match f7():
        T1.A: ()
        T1.B: ()


f18():
    match f7():
        T2.A: ()
        T2.B: ()


f19():
    match f7():
        T3.A: ()
        T3.B: ()


# args: --typecheck
