prim type I32

impl Add for I32:
    prim __add(self, other: I32): I32

impl Sub for I32:
    prim __sub(self, other: I32): I32

impl Mul for I32:
    prim __mul(self, other: I32): I32

impl Div for I32:
    prim __div(self, other: I32): I32

impl Eq for I32:
    prim __eq(self, other: I32): Bool

impl Ord for I32:
    prim cmp(self, other: I32): Ordering

impl BitAnd for I32:
    prim __bitand(self, other: I32): I32

impl BitOr for I32:
    prim __bitor(self, other: I32): I32

impl Shl for I32:
    prim __shl(self, shift: I32): I32

impl Shr for I32:
    prim __shr(self, shift: I32): I32

impl Neg for I32:
    prim __neg(self): I32

impl ToStr for I32:
    prim toStr(self): Str

impl Step for I32:
    next(self): I32 = self + 1

prim type U32

impl Add for U32:
    prim __add(self, other: U32): U32

impl Sub for U32:
    prim __sub(self, other: U32): U32

impl Mul for U32:
    prim __mul(self, other: U32): U32

impl Div for U32:
    prim __div(self, other: U32): U32

impl Eq for U32:
    prim __eq(self, other: U32): Bool

impl Ord for U32:
    prim cmp(self, other: U32): Ordering

impl BitAnd for U32:
    prim __bitand(self, other: U32): U32

impl BitOr for U32:
    prim __bitor(self, other: U32): U32

impl Shl for U32:
    prim __shl(self, shift: U32): U32

impl Shr for U32:
    prim __shr(self, shift: U32): U32

impl ToStr for U32:
    prim toStr(self): Str

impl Step for U32:
    next(self): U32 = self + 1

prim type I8

impl Add for I8:
    prim __add(self, other: I8): I8

impl Sub for I8:
    prim __sub(self, other: I8): I8

impl Mul for I8:
    prim __mul(self, other: I8): I8

impl Div for I8:
    prim __div(self, other: I8): I8

impl Eq for I8:
    prim __eq(self, other: I8): Bool

impl Ord for I8:
    prim cmp(self, other: I8): Ordering

impl BitAnd for I8:
    prim __bitand(self, other: I8): I8

impl BitOr for I8:
    prim __bitor(self, other: I8): I8

impl Shl for I8:
    prim __shl(self, shift: I8): I8

impl Shr for I8:
    prim __shr(self, shift: I8): I8

impl Neg for I8:
    prim __neg(self): I8

impl ToStr for I8:
    prim toStr(self): Str

impl Step for I8:
    next(self): I8 = self + 1

prim type U8

impl Add for U8:
    prim __add(self, other: U8): U8

impl Sub for U8:
    prim __sub(self, other: U8): U8

impl Mul for U8:
    prim __mul(self, other: U8): U8

impl Div for U8:
    prim __div(self, other: U8): U8

impl Eq for U8:
    prim __eq(self, other: U8): Bool

impl Ord for U8:
    prim cmp(self, other: U8): Ordering

impl BitAnd for U8:
    prim __bitand(self, other: U8): U8

impl BitOr for U8:
    prim __bitor(self, other: U8): U8

impl Shl for U8:
    prim __shl(self, shift: U8): U8

impl Shr for U8:
    prim __shr(self, shift: U8): U8

impl ToStr for U8:
    prim toStr(self): Str

impl Step for U8:
    next(self): U8 = self + 1

################################################################################
#
# Conversions
#
################################################################################

prim U8.asI8(self): I8
prim U8.asI32(self): I32
prim U8.asU32(self): U32

prim I8.asU8(self): U8
prim I8.asI32(self): I32
prim I8.asU32(self): U32
prim I8.abs(self): I8

prim U32.asI8(self): I8
prim U32.asU8(self): U8
prim U32.asI32(self): I32

prim I32.asI8(self): I8
prim I32.asU8(self): U8
prim I32.asU32(self): U32
prim I32.abs(self): I32
