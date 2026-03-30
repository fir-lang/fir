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


impl ToStr[[]]:
    toStr(self: []) Str:
        "unreachable"


impl ToDoc[[]]:
    toDoc(self: []) Doc:
        panic("unreachable")


impl Eq[[]]:
    __eq(self: [], other: []) Bool:
        panic("unreachable")

    __neq(self: [], other: []) Bool:
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
    type List

    rowToList(rec: (..recRow)) Option[List]


value type ListCons[head, tail](
    head: head,
    tail: Option[tail],
)


impl[ToStr[head], ToStr[tail]] ToStr[ListCons[head, tail]]:
    toStr(self: ListCons[head, tail]) Str:
        match self.tail:
            Option.None: "`self.head`"
            Option.Some(t): "`self.head`, `t`"


impl[ToDoc[head], ToDoc[tail]] ToDoc[ListCons[head, tail]]:
    toDoc(self: ListCons[head, tail]) Doc:
        match self.tail:
            Option.None: self.head.toDoc() + Doc.whenNotFlat(Doc.char(','))
            Option.Some(t):
                self.head.toDoc() + Doc.char(',') + Doc.break_(1) + t.toDoc()


impl[Eq[head], Eq[tail]] Eq[ListCons[head, tail]]:
    __eq(self: ListCons[head, tail], other: ListCons[head, tail]) Bool:
        self.head == other.head and self.tail == other.tail


type RecordField[t](
    label: Str,
    value_: t,
)


impl[ToStr[t]] ToStr[RecordField[t]]:
    toStr(self: RecordField[t]) Str:
        "`self.label` = `self.value_`"


impl[ToDoc[t]] ToDoc[RecordField[t]]:
    toDoc(self: RecordField[t]) Doc:
        Doc.str(self.label)
            + Doc.blank(1)
            + Doc.char('=')
            + Doc.blank(1)
            + self.value_.toDoc()


impl[Eq[t]] Eq[RecordField[t]]:
    __eq(self: RecordField[t], other: RecordField[t]) Bool:
        self.label == other.label and self.value_ == other.value_


impl[ToStr[RowToList[r].List]] ToStr[(..r)]:
    toStr(self: (..r)) Str:
        match RowToList[r].rowToList(self):
            Option.None: "()"
            Option.Some(list): "(`list`)"


impl[ToDoc[RowToList[r].List]] ToDoc[(..r)]:
    toDoc(self: (..r)) Doc:
        match RowToList[r].rowToList(self):
            Option.None: Doc.str("()")
            Option.Some(list):
                Doc.grouped(
                    Doc.nested(4, Doc.char('(') + Doc.break_(0) + list.toDoc())
                        + Doc.break_(0)
                        + Doc.char(')'),
                )


impl[Eq[RowToList[r].List]] Eq[(..r)]:
    __eq(self: (..r), other: (..r)) Bool:
        RowToList[r].rowToList(self) == RowToList[r].rowToList(other)

    # Explicitly implement `__neq`, the default method calls a method on `self` and we don't support
    # method calls on records yet.
    __neq(self: (..r), other: (..r)) Bool:
        not (RowToList[r].rowToList(self) == RowToList[r].rowToList(other))
