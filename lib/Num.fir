prim type I32

impl ToStrView[I32]:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

impl Add[I32]:
    prim fn __add(self, other: I32): I32

impl Sub[I32]:
    prim fn __sub(self, other: I32): I32

impl Mul[I32]:
    prim fn __mul(self, other: I32): I32

impl Div[I32]:
    prim fn __div(self, other: I32): I32

impl Eq[I32]:
    prim fn __eq(self, other: I32): Bool

impl Ord[I32]:
    prim fn cmp(self, other: I32): Ordering

impl I32:
    prim fn toStr(self): Str

prim type U32

impl ToStrView[U32]:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

impl Add[U32]:
    prim fn __add(self, other: U32): U32

impl Sub[U32]:
    prim fn __sub(self, other: U32): U32

impl Mul[U32]:
    prim fn __mul(self, other: U32): U32

impl Div[U32]:
    prim fn __div(self, other: U32): U32

impl Eq[U32]:
    prim fn __eq(self, other: U32): Bool

impl Ord[U32]:
    prim fn cmp(self, other: U32): Ordering

impl U32:
    prim fn toStr(self): Str

prim type I8

impl ToStrView[I8]:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

impl Add[I8]:
    prim fn __add(self, other: I8): I8

impl Sub[I8]:
    prim fn __sub(self, other: I8): I8

impl Mul[I8]:
    prim fn __mul(self, other: I8): I8

impl Div[I8]:
    prim fn __div(self, other: I8): I8

impl Eq[I8]:
    prim fn __eq(self, other: I8): Bool

impl Ord[I8]:
    prim fn cmp(self, other: I8): Ordering

impl I8:
    prim fn toStr(self): Str

prim type U8

impl ToStrView[U8]:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

impl Add[U8]:
    prim fn __add(self, other: U8): U8

impl Sub[U8]:
    prim fn __sub(self, other: U8): U8

impl Mul[U8]:
    prim fn __mul(self, other: U8): U8

impl Div[U8]:
    prim fn __div(self, other: U8): U8

impl Eq[U8]:
    prim fn __eq(self, other: U8): Bool

impl Ord[U8]:
    prim fn cmp(self, other: U8): Ordering

impl U8:
    prim fn toStr(self): Str
