import Char
import Exn
import Iter
import Num
import Str
import StrBuf
import Vec

# The `+` operator.
trait Add[t]:
    __add(self, other: t): t

# The `-` operator.
trait Sub[t]:
    __sub(self, other: t): t

# The unary `-` operator.
trait Neg[t]:
    __neg(self): t

# The `*` operator.
trait Mul[t]:
    __mul(self, other: t): t

# The `/` operator.
trait Div[t]:
    __div(self, other: t): t

# The `==` operator.
trait Eq[t]:
    __eq(self, other: t): Bool

    __neq(self, other: t): Bool
        !self.__eq(other)

# The `|` operator.
trait BitOr[t]:
    __bitor(self, other: t): t

# The `&` operator.
trait BitAnd[t]:
    __bitand(self, other: t): t

# The `<<` operator.
trait Shl[t]:
    __shl(self, other: t): t

# The `>>` operator.
trait Shr[t]:
    __shr(self, other: t): t

trait Ord[t]:
    cmp(self, other: t): Ordering

    __lt(self, other: t): Bool
        match self.cmp(other):
            Ordering.Less: Bool.True
            _: Bool.False

    __le(self, other: t): Bool
        match self.cmp(other):
            Ordering.Less | Ordering.Equal: Bool.True
            _: Bool.False

    __gt(self, other: t): Bool
        match self.cmp(other):
            Ordering.Greater: Bool.True
            _: Bool.False

    __ge(self, other: t): Bool
        match self.cmp(other):
            Ordering.Greater | Ordering.Equal: Bool.True
            _: Bool.False

trait ToStr[t]:
    toStr(self): Str

# The bottom type, e.g. return type of a function that doesn't return.
# We may want to rename this later.
type Void

prim type Array[t]

prim Array[t].new(len: U32): Array[t]
prim Array[t].len(self): U32
prim Array[t].get(self, idx: U32): t
prim Array[t].set(self, idx: U32, elem: t)

impl[t: ToStr] ToStr for Array[t]:
    toStr(self): Str
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i in range(0u32, self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()

prim printStr(s: Str)
prim panic[t: ToStr](msg: t): Void

type Option[t]:
    None
    Some(t)

impl[t: ToStr] ToStr for Option[t]:
    toStr(self): Str
        match self:
            Option.None: "Option.None"
            Option.Some(t): "Option.Some(`t.toStr()`)"

Option[t].unwrap(self): t
    match self:
        Option.None: panic("Unwrapping Option.None")
        Option.Some(value): value

type Result[e, t]:
    Err(e)
    Ok(t)

impl[e: ToStr, t: ToStr] ToStr for Result[e, t]:
    toStr(self): Str
        match self:
            Result.Err(e): "Result.Err(`e.toStr()`)"
            Result.Ok(t): "Result.Ok(`t.toStr()`)"

Result[e, t].mapErr(self, f: Fn(e): e2): Result[e2, t]
    match self:
        Result.Ok(a): Result.Ok(a)
        Result.Err(e): Result.Err(f(e))

type Ordering:
    Less
    Equal
    Greater

impl ToStr for Ordering:
    toStr(self): Str
        match self:
            Ordering.Less: "Ordering.Less"
            Ordering.Equal: "Ordering.Equal"
            Ordering.Greater: "Ordering.Greater"

type Bool:
    False
    True

impl ToStr for Bool:
    toStr(self): Str
        match self:
            Bool.True: "Bool.True"
            Bool.False: "Bool.False"

prim readFileUtf8(path: Str): Str
