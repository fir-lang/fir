prim type I32

impl Add for I32:
    prim fn __add(self, other: I32): I32

impl Sub for I32:
    prim fn __sub(self, other: I32): I32

impl Mul for I32:
    prim fn __mul(self, other: I32): I32

impl Div for I32:
    prim fn __div(self, other: I32): I32

impl Eq for I32:
    prim fn __eq(self, other: I32): Bool

impl Ord for I32:
    prim fn cmp(self, other: I32): Ordering

impl BitAnd for I32:
    prim fn __bitand(self, other: I32): I32

impl BitOr for I32:
    prim fn __bitor(self, other: I32): I32

impl Shl for I32:
    prim fn __shl(self, shift: I32): I32

impl Shr for I32:
    prim fn __shr(self, shift: I32): I32

impl ToStr for I32:
    prim fn toStr(self): Str

impl Step for I32:
    fn next(self): I32 = self + 1

prim type U32

impl Add for U32:
    prim fn __add(self, other: U32): U32

impl Sub for U32:
    prim fn __sub(self, other: U32): U32

impl Mul for U32:
    prim fn __mul(self, other: U32): U32

impl Div for U32:
    prim fn __div(self, other: U32): U32

impl Eq for U32:
    prim fn __eq(self, other: U32): Bool

impl Ord for U32:
    prim fn cmp(self, other: U32): Ordering

impl BitAnd for U32:
    prim fn __bitand(self, other: U32): U32

impl BitOr for U32:
    prim fn __bitor(self, other: U32): U32

impl Shl for U32:
    prim fn __shl(self, shift: U32): U32

impl Shr for U32:
    prim fn __shr(self, shift: U32): U32

impl ToStr for U32:
    prim fn toStr(self): Str

impl Step for U32:
    fn next(self): U32 = self + 1

prim type I8

impl Add for I8:
    prim fn __add(self, other: I8): I8

impl Sub for I8:
    prim fn __sub(self, other: I8): I8

impl Mul for I8:
    prim fn __mul(self, other: I8): I8

impl Div for I8:
    prim fn __div(self, other: I8): I8

impl Eq for I8:
    prim fn __eq(self, other: I8): Bool

impl Ord for I8:
    prim fn cmp(self, other: I8): Ordering

impl BitAnd for I8:
    prim fn __bitand(self, other: I8): I8

impl BitOr for I8:
    prim fn __bitor(self, other: I8): I8

impl Shl for I8:
    prim fn __shl(self, shift: I8): I8

impl Shr for I8:
    prim fn __shr(self, shift: I8): I8

impl ToStr for I8:
    prim fn toStr(self): Str

impl Step for I8:
    fn next(self): I8 = self + 1

prim type U8

impl Add for U8:
    prim fn __add(self, other: U8): U8

impl Sub for U8:
    prim fn __sub(self, other: U8): U8

impl Mul for U8:
    prim fn __mul(self, other: U8): U8

impl Div for U8:
    prim fn __div(self, other: U8): U8

impl Eq for U8:
    prim fn __eq(self, other: U8): Bool

impl Ord for U8:
    prim fn cmp(self, other: U8): Ordering

impl BitAnd for U8:
    prim fn __bitand(self, other: U8): U8

impl BitOr for U8:
    prim fn __bitor(self, other: U8): U8

impl Shl for U8:
    prim fn __shl(self, shift: U8): U8

impl Shr for U8:
    prim fn __shr(self, shift: U8): U8

impl ToStr for U8:
    prim fn toStr(self): Str

impl Step for U8:
    fn next(self): U8 = self + 1
