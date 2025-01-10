import Char
import Iter
import Num
import Str
import StrBuf
import Vec

# The `+` operator.
trait Add[t]:
    fn __add(self, other: t): t

# The `-` operator.
trait Sub[t]:
    fn __sub(self, other: t): t

# The `*` operator.
trait Mul[t]:
    fn __mul(self, other: t): t

# The `/` operator.
trait Div[t]:
    fn __div(self, other: t): t

# The `==` operator.
trait Eq[t]:
    fn __eq(self, other: t): Bool

    fn __neq(self, other: t): Bool
        !self.__eq(other)

# The `|` operator.
trait BitOr[t]:
    fn __bitor(self, other: t): t

# The `&` operator.
trait BitAnd[t]:
    fn __bitand(self, other: t): t

# The `<<` operator.
trait Shl[t]:
    fn __shl(self, other: t): t

# The `>>` operator.
trait Shr[t]:
    fn __shr(self, other: t): t

trait Ord[t]:
    fn cmp(self, other: t): Ordering

    fn __lt(self, other: t): Bool
        match self.cmp(other):
            Ordering.Less: Bool.True
            _: Bool.False

    fn __le(self, other: t): Bool
        match self.cmp(other):
            Ordering.Less | Ordering.Equal: Bool.True
            _: Bool.False

    fn __gt(self, other: t): Bool
        match self.cmp(other):
            Ordering.Greater: Bool.True
            _: Bool.False

    fn __ge(self, other: t): Bool
        match self.cmp(other):
            Ordering.Greater | Ordering.Equal: Bool.True
            _: Bool.False

trait ToStr[t]:
    fn toStr(self): Str

# The bottom type, e.g. return type of a function that doesn't return.
# We may want to rename this later.
type Void

prim type Array[t]

impl Array[t]:
    prim fn new(len: U32): Array[t]
    prim fn len(self): U32
    prim fn get(self, idx: U32): t
    prim fn set(self, idx: U32, elem: t)

prim fn printStr(s: Str)
prim fn panic[t: ToStr](msg: t): Void

type Option[t]:
    None
    Some(t)

impl[t] Option[t]:
    fn unwrap(self): t
        match self:
            Option.None: panic("Unwrapping Option.None")
            Option.Some(value): value

type Result[e, t]:
    Err(e)
    Ok(t)

type Ordering:
    Less
    Equal
    Greater

type Bool:
    False
    True

impl ToStr for Bool:
    fn toStr(self): Str
        match self:
            Bool.True: "Bool.True"
            Bool.False: "Bool.False"
