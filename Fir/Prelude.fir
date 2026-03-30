import [
    Fir/Array,
    Fir/Char,
    Fir/Deque,
    Fir/Exn,
    Fir/HashMap,
    Fir/HashSet,
    Fir/Iter,
    Fir/Num,
    Fir/Option,
    Fir/PPrint,
    Fir/Result,
    Fir/Str,
    Fir/StrBuf,
    Fir/Vec,
]


## The `+` operator.
trait Add[t]:
    __add(self: t, other: t) t


## The `-` operator.
trait Sub[t]:
    __sub(self: t, other: t) t


## The unary `-` operator.
trait Neg[t]:
    __neg(self: t) t


## The `*` operator.
trait Mul[t]:
    __mul(self: t, other: t) t


## The `/` operator.
trait Div[t]:
    __div(self: t, other: t) t


## The `==` operator.
trait Eq[t]:
    __eq(self: t, other: t) Bool

    __neq(self: t, other: t) Bool:
        not self.__eq(other)


## The `|` operator.
trait BitOr[t]:
    __bitor(self: t, other: t) t


## The `^` operator.
trait BitXor[t]:
    __bitxor(self: t, other: t) t


## The `&` operator.
trait BitAnd[t]:
    __bitand(self: t, other: t) t


## The `<<` operator.
trait Shl[t]:
    __shl(self: t, other: t) t


## The `>>` operator.
trait Shr[t]:
    __shr(self: t, other: t) t


## The remainder operation: `n % d == n - ((n / d) * d)`.
##
## For signed numbers, the result will have the same sign as the dividend.
##
## For now this doesn't have a syntax. In the future we will probably desugar
## `%` to this.
trait Rem[t]:
    rem(self: t, divisor: t) t


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


max[Ord[t]](a: t, b: t) t:
    if a > b:
        a
    else:
        b


min[Ord[t]](a: t, b: t) t:
    if a < b:
        a
    else:
        b


trait ToStr[t]:
    toStr(self: t) Str


impl ToStr[()]:
    toStr(self: ()) Str:
        "()"


impl ToDoc[()]:
    toDoc(self: ()) Doc:
        Doc.str("()")


impl ToStr[[]]:
    toStr(self: []) Str:
        "unreachable"


impl ToDoc[[]]:
    toDoc(self: []) Doc:
        panic("unreachable")


trait ToDoc[t]:
    toDoc(self: t) Doc


impl ToDoc[Doc]:
    toDoc(self: Doc) Doc:
        self


prim printStrNoNl(s: Str)


printStr(s: Str):
    printStrNoNl(s)
    printStrNoNl("\n")


print[ToStr[a]](a: a):
    printStr(a.toStr())


printNoNl[ToStr[a]](a: a):
    printStrNoNl(a.toStr())


prim panic(msg: Str) a


value type Ordering:
    Less
    Equal
    Greater


impl ToStr[Ordering]:
    toStr(self: Ordering) Str:
        match self:
            Ordering.Less: "Ordering.Less"
            Ordering.Equal: "Ordering.Equal"
            Ordering.Greater: "Ordering.Greater"


value type Bool:
    False
    True


Bool.__not(self) Bool:
    match self:
        Bool.True: Bool.False
        Bool.False: Bool.True


impl Eq[Bool]:
    __eq(self: Bool, other: Bool) Bool:
        match self:
            Bool.True: other
            Bool.False: not other


impl ToStr[Bool]:
    toStr(self: Bool) Str:
        match self:
            Bool.True: "Bool.True"
            Bool.False: "Bool.False"


impl ToDoc[Bool]:
    toDoc(self: Bool) Doc:
        Doc.str(self.toStr())


prim readFileUtf8(path: Str) Str


## Get command line arguments passed to the program.
prim getArgs() Array[Str]


trait Hash[t]:
    hash(self: t) U32


trait Clone[t]:
    clone(self: t) t


# This trait will only be implemented by the compiler, for record types, as
# needed.
trait RowToList[recRow]:
    # This will always be `ListCons` or `ListNil`.
    type List

    rowToList(rec: (..recRow)) List


value type ListCons[head, tail](
    head: head,
    tail: tail,
)


value type ListNil


impl ToStr[ListNil]:
    toStr(self: ListNil) Str:
        ""


impl[ToStr[head], ToStr[tail]] ToStr[ListCons[head, tail]]:
    toStr(self: ListCons[head, tail]) Str:
        "`self.head`, `self.tail`"


type RecordField[t](
    label: Str,
    value_: t,
)


impl[ToStr[t]] ToStr[RecordField[t]]:
    toStr(self: RecordField[t]) Str:
        "`self.label` = `self.value_`"


impl[ToStr[RowToList[r].List]] ToStr[(..r)]:
    toStr(self: (..r)) Str:
        let list = RowToList[r].rowToList(self)
        "(`list`)"
