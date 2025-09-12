import Fir.Array
import Fir.Char
import Fir.Exn
import Fir.HashMap
import Fir.Iter
import Fir.Num
import Fir.Option
import Fir.PPrint
import Fir.Result
import Fir.Str
import Fir.StrBuf
import Fir.Vec


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
    __add(self: t, other: t) t


# The `-` operator.
trait Sub[t]:
    __sub(self: t, other: t) t


# The unary `-` operator.
trait Neg[t]:
    __neg(self: t) t


# The `*` operator.
trait Mul[t]:
    __mul(self: t, other: t) t


# The `/` operator.
trait Div[t]:
    __div(self: t, other: t) t


# The `==` operator.
trait Eq[t]:
    __eq(self: t, other: t) Bool

    __neq(self: t, other: t) Bool:
        not self.__eq(other)


# The `|` operator.
trait BitOr[t]:
    __bitor(self: t, other: t) t


# The `^` operator.
trait BitXor[t]:
    __bitxor(self: t, other: t) t


# The `&` operator.
trait BitAnd[t]:
    __bitand(self: t, other: t) t


# The `<<` operator.
trait Shl[t]:
    __shl(self: t, other: t) t


# The `>>` operator.
trait Shr[t]:
    __shr(self: t, other: t) t


trait Ord[t]:
    cmp(self: t, other: t) Ordering

    __lt(self: t, other: t) Bool:
        match self.cmp(other):
            Ordering.Less: Bool.True
            _: Bool.False

    __le(self: t, other: t) Bool:
        match self.cmp(other):
            Ordering.Less | Ordering.Equal: Bool.True
            _: Bool.False

    __gt(self: t, other: t) Bool:
        match self.cmp(other):
            Ordering.Greater: Bool.True
            _: Bool.False

    __ge(self: t, other: t) Bool:
        match self.cmp(other):
            Ordering.Greater | Ordering.Equal: Bool.True
            _: Bool.False


trait ToStr[t]:
    toStr(self: t) Str


impl ToStr[()]:
    toStr(self: ()) Str:
        "()"


prim printStrNoNl(s: Str)


printStr(s: Str):
    printStrNoNl(s)
    printStrNoNl("\n")


print[ToStr[a]](a: a):
    printStr(a.toStr())


printNoNl[ToStr[a]](a: a):
    printStrNoNl(a.toStr())


prim panic(msg: Str) a


type Ordering:
    Less
    Equal
    Greater


impl ToStr[Ordering]:
    toStr(self: Ordering) Str:
        match self:
            Ordering.Less: "Ordering.Less"
            Ordering.Equal: "Ordering.Equal"
            Ordering.Greater: "Ordering.Greater"


type Bool:
    False
    True


Bool.__not(self) Bool:
    match self:
        Bool.True: Bool.False
        Bool.False: Bool.True


impl ToStr[Bool]:
    toStr(self: Bool) Str:
        match self:
            Bool.True: "Bool.True"
            Bool.False: "Bool.False"


prim readFileUtf8(path: Str) Str


trait Hash[t]:
    hash(self: t) U32


trait Clone[t]:
    clone(self: t) t
