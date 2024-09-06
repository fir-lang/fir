# The `+` operator.
trait Add[T]:
    fn __add(self, other: T): T

# The `-` operator.
trait Sub[T]:
    fn __sub(self, other: T): T

# The `*` operator.
trait Mul[T]:
    fn __mul(self, other: T): T

# The `/` operator.
trait Div[T]:
    fn __div(self, other: T): T

# The `==` operator.
trait Eq[T]:
    fn __eq(self, other: T): Bool

    fn __neq(self, other: T): Bool =
        !self.__eq(other)

trait Ord[T]:
    fn cmp(self, other: T): Ordering

    fn __lt(self, other: T): Bool =
        match self.cmp(other):
            Ordering.Less: Bool.True
            _: Bool.False

    fn __le(self, other: T): Bool =
        match self.cmp(other):
            Ordering.Less | Ordering.Equal: Bool.True
            _: Bool.False

    fn __gt(self, other: T): Bool =
        match self.cmp(other):
            Ordering.Greater: Bool.True
            _: Bool.False

    fn __ge(self, other: T): Bool =
        match self.cmp(other):
            Ordering.Greater | Ordering.Equal: Bool.True
            _: Bool.False

# Just to be able to pass `Str` where `StrView` is expected.
trait ToStrView[T]:
    fn toStrView(self): StrView

# The bottom type, e.g. return type of a function that doesn't return.
# We may want to rename this later.
type Void

prim type Str

impl Eq[Str]:
    prim fn __eq(self, other: Str): Bool

impl Str:
    prim fn len(self): I32
    prim fn substr(self, byteStart: I32, byteEnd: I32): StrView

impl ToStrView[Str]:
    fn toStrView(self): StrView =
        self.substr(0, self.len())

prim type StrView

impl ToStrView[StrView]:
    fn toStrView(self): StrView =
        self

impl Eq[StrView]:
    prim fn __eq(self, other: StrView): Bool

impl StrView:
    prim fn isEmpty(self): Bool
    prim fn len(self): I32
    prim fn startsWith(self, str: Str): Bool    # TODO: Argument should be StrView
    prim fn substr(self, byteStart: I32, byteEnd: I32): StrView
    prim fn toStr(self): Str

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

prim type Array[T]

impl[T] Array[T]:
    prim fn new(len: I32): Array[T]
    prim fn len(self): I32
    prim fn get(self, idx: I32): T
    prim fn set(self, idx: I32, elem: T)

prim fn printStr(s: Str)
prim fn printStrView(s: StrView)
prim fn panic[T: ToStrView](msg: T): Void

type Option[T]:
    None
    Some(T)

type Result[E, T]:
    Err(E)
    Ok(T)

type Ordering:
    Less
    Equal
    Greater

type Bool:
    False
    True

impl Bool:
    fn __and(self, other: Bool): Bool =
        match self:
            Bool.False: Bool.False
            Bool.True: other

    fn __or(self, other: Bool): Bool =
        match self:
            Bool.True: Bool.True
            Bool.False: other

    fn toStr(self): Str =
        match self:
            Bool.True: "Bool.True"
            Bool.False: "Bool.False"

impl ToStrView[Bool]:
    fn toStrView(self): StrView =
        self.toStr().toStrView()

# TODO: We may want to allow unnamed fields: `type Char(U32)`.
type Char:
    value: I32 # TODO: Switch to U32 when we have it.

impl Eq[Char]:
    fn __eq(self, other: Char): Bool =
        self.value == other.value

type Vec[T]:
    data: Array[T]
    len: I32

impl[T] Vec[T]:
    fn withCapacity(cap: I32): Vec[T] =
        Vec(data = Array.new(cap), len = 0)

    fn len(self): I32 =
        self.len

    fn push(self, elem: T) =
        let cap = self.data.len()

        if self.len == cap:
            let newData = Array.new(cap * 2)
            for i in 0 .. cap:
                newData.set(i, self.data.get(i))
            self.data = newData

        self.data.set(self.len, elem)
        self.len += 1

    fn pop(self): Option[T] =
        if self.len == 0:
            return Option.None

        self.len -= 1
        Option.Some(self.data.get(self.len))

    fn set(self, idx: I32, elem: T) =
        if idx >= self.len:
            panic("Vec.set OOB (len=`self.len.toStr()`, idx=`idx.toStr()`)")

        self.data.set(idx, elem)

    fn get(self, idx: I32): T =
        if idx >= self.len:
            panic("Vec.get OOB (len=`self.len.toStr()`, idx=`idx.toStr()`)")

        self.data.get(idx)
