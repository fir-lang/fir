prim type I32

impl ToStrView for I32:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

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

impl I32:
    prim fn toStr(self): Str

prim type U32

impl ToStrView for U32:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

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

impl U32:
    prim fn toStr(self): Str

prim type I8

impl ToStrView for I8:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

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

impl I8:
    prim fn toStr(self): Str

prim type U8

impl ToStrView for U8:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

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

impl U8:
    prim fn toStr(self): Str
