fn test[R](r: (x: I32, y: I32 | R)) = ()

fn main() =
    test((x = 1, y = 2))

##################################################

prim type I32

type Bool:
    True
    False

prim type Char

prim type Str

prim type Ordering

prim type I8

prim type U8

prim type U32

prim type Array[T]
