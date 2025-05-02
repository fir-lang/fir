import Char
import Exn
import HashMap
import Iter
import Num
import Option
import PPrint
import Result
import Str
import StrBuf
import Vec

# A marker trait used to mark a type parameter as a record row.
#
# This is temporary until we implement kind inference. (#46)
trait RecRow[t]

# A marker trait used to mark a type parameter as a variant row.
#
# This is temporary until we implement kind inference. (#46)
trait VarRow[t]

# The `+` operator.
trait Add[t]:
    __add(self: t, other: t): t

# The `-` operator.
trait Sub[t]:
    __sub(self: t, other: t): t

# The unary `-` operator.
trait Neg[t]:
    __neg(self: t): t

# The `*` operator.
trait Mul[t]:
    __mul(self: t, other: t): t

# The `/` operator.
trait Div[t]:
    __div(self: t, other: t): t

# The `==` operator.
trait Eq[t]:
    __eq(self: t, other: t): Bool

    __neq(self: t, other: t): Bool
        !self.__eq(other)

# The `|` operator.
trait BitOr[t]:
    __bitor(self: t, other: t): t

# The `^` operator.
trait BitXor[t]:
    __bitxor(self: t, other: t): t

# The `&` operator.
trait BitAnd[t]:
    __bitand(self: t, other: t): t

# The `<<` operator.
trait Shl[t]:
    __shl(self: t, other: t): t

# The `>>` operator.
trait Shr[t]:
    __shr(self: t, other: t): t

trait Ord[t]:
    cmp(self: t, other: t): Ordering

    __lt(self: t, other: t): Bool
        match self.cmp(other):
            Ordering.Less: Bool.True
            _: Bool.False

    __le(self: t, other: t): Bool
        match self.cmp(other):
            Ordering.Less | Ordering.Equal: Bool.True
            _: Bool.False

    __gt(self: t, other: t): Bool
        match self.cmp(other):
            Ordering.Greater: Bool.True
            _: Bool.False

    __ge(self: t, other: t): Bool
        match self.cmp(other):
            Ordering.Greater | Ordering.Equal: Bool.True
            _: Bool.False

trait ToStr[t]:
    toStr(self: t): Str

# The bottom type, e.g. return type of a function that doesn't return.
# We may want to rename this later.
type Void

prim type Array[t]

prim Array.new(len: U32): Array[t]
prim Array.len(self: Array[t]): U32
prim Array.get(self: Array[t], idx: U32): t
prim Array.set(self: Array[t], idx: U32, elem: t)

impl[ToStr[t]] ToStr[Array[t]]:
    toStr(self: Array[t]): Str
        let buf = StrBuf.withCapacity(self.len() * 5 + 2)
        buf.push('[')
        for i: U32 in range(0u32, self.len()):
            if i != 0:
                buf.push(',')
            buf.pushStr(self.get(i).toStr())
        buf.push(']')
        buf.toStr()

prim printStrNoNl(s: Str)

printStr(s: Str)
    printStrNoNl(s)
    printStrNoNl("\n")

print[ToStr[a]](a: a) = printStr(a.toStr())

printNoNl[ToStr[a]](a: a) = printStrNoNl(a.toStr())

prim panic[ToStr[t]](msg: t): Void

type Ordering:
    Less
    Equal
    Greater

impl ToStr[Ordering]:
    toStr(self: Ordering): Str
        match self:
            Ordering.Less: "Ordering.Less"
            Ordering.Equal: "Ordering.Equal"
            Ordering.Greater: "Ordering.Greater"

type Bool:
    False
    True

impl ToStr[Bool]:
    toStr(self: Bool): Str
        match self:
            Bool.True: "Bool.True"
            Bool.False: "Bool.False"

prim readFileUtf8(path: Str): Str

trait Hash[t]:
    hash(self: t): U32
