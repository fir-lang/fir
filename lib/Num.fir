prim type I32

impl Add[I32]:
    prim __add(self, other: I32): I32

impl Sub[I32]:
    prim __sub(self, other: I32): I32

impl Mul[I32]:
    prim __mul(self, other: I32): I32

impl Div[I32]:
    prim __div(self, other: I32): I32

impl Eq[I32]:
    prim __eq(self, other: I32): Bool

impl Ord[I32]:
    prim cmp(self, other: I32): Ordering

impl BitAnd[I32]:
    prim __bitand(self, other: I32): I32

impl BitOr[I32]:
    prim __bitor(self, other: I32): I32

impl Shl[I32]:
    prim __shl(self, shift: I32): I32

impl Shr[I32]:
    prim __shr(self, shift: I32): I32

impl Neg[I32]:
    prim __neg(self): I32

impl ToStr[I32]:
    prim toStr(self): Str

impl Step[I32]:
    next(self): I32 = self + 1

prim type U32

impl Add[U32]:
    prim __add(self, other: U32): U32

impl Sub[U32]:
    prim __sub(self, other: U32): U32

impl Mul[U32]:
    prim __mul(self, other: U32): U32

impl Div[U32]:
    prim __div(self, other: U32): U32

impl Eq[U32]:
    prim __eq(self, other: U32): Bool

impl Ord[U32]:
    prim cmp(self, other: U32): Ordering

impl BitAnd[U32]:
    prim __bitand(self, other: U32): U32

impl BitOr[U32]:
    prim __bitor(self, other: U32): U32

impl Shl[U32]:
    prim __shl(self, shift: U32): U32

impl Shr[U32]:
    prim __shr(self, shift: U32): U32

impl ToStr[U32]:
    prim toStr(self): Str

impl Step[U32]:
    next(self): U32 = self + 1

prim type I8

impl Add[I8]:
    prim __add(self, other: I8): I8

impl Sub[I8]:
    prim __sub(self, other: I8): I8

impl Mul[I8]:
    prim __mul(self, other: I8): I8

impl Div[I8]:
    prim __div(self, other: I8): I8

impl Eq[I8]:
    prim __eq(self, other: I8): Bool

impl Ord[I8]:
    prim cmp(self, other: I8): Ordering

impl BitAnd[I8]:
    prim __bitand(self, other: I8): I8

impl BitOr[I8]:
    prim __bitor(self, other: I8): I8

impl Shl[I8]:
    prim __shl(self, shift: I8): I8

impl Shr[I8]:
    prim __shr(self, shift: I8): I8

impl Neg[I8]:
    prim __neg(self): I8

impl ToStr[I8]:
    prim toStr(self): Str

impl Step[I8]:
    next(self): I8 = self + 1

prim type U8

impl Add[U8]:
    prim __add(self, other: U8): U8

impl Sub[U8]:
    prim __sub(self, other: U8): U8

impl Mul[U8]:
    prim __mul(self, other: U8): U8

impl Div[U8]:
    prim __div(self, other: U8): U8

impl Eq[U8]:
    prim __eq(self, other: U8): Bool

impl Ord[U8]:
    prim cmp(self, other: U8): Ordering

impl BitAnd[U8]:
    prim __bitand(self, other: U8): U8

impl BitOr[U8]:
    prim __bitor(self, other: U8): U8

impl Shl[U8]:
    prim __shl(self, shift: U8): U8

impl Shr[U8]:
    prim __shr(self, shift: U8): U8

impl ToStr[U8]:
    prim toStr(self): Str

impl Step[U8]:
    next(self): U8 = self + 1

################################################################################
#
# Conversions
#
################################################################################

prim U8.asI8(self: U8): I8
prim U8.asI32(self: U8): I32
prim U8.asU32(self: U8): U32

prim I8.asU8(self: I8): U8
prim I8.asI32(self: I8): I32
prim I8.asU32(self: I8): U32
prim I8.abs(self: I8): I8

prim U32.asI8(self: U32): I8
prim U32.asU8(self: U32): U8
prim U32.asI32(self: U32): I32

prim I32.asI8(self: U32): I8
prim I32.asU8(self: U32): U8
prim I32.asU32(self: U32): U32
prim I32.abs(self: U32): I32
