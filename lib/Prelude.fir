import Char
import Num
import Str
import StrBuf
import Vec

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

# The `|` operator.
trait BitOr[T]:
    fn __bitor(self, other: T): T

# The `&` operator.
trait BitAnd[T]:
    fn __bitand(self, other: T): T

# The `<<` operator.
trait Shl[T]:
    fn __shl(self, other: T): T

# The `>>` operator.
trait Shr[T]:
    fn __shr(self, other: T): T

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

trait ToStr[T]:
    fn toStr(self): Str

# The bottom type, e.g. return type of a function that doesn't return.
# We may want to rename this later.
type Void

prim type Array[T]

impl[T] Array[T]:
    prim fn new(len: U32): Array[T]
    prim fn len(self): U32
    prim fn get(self, idx: U32): T
    prim fn set(self, idx: U32, elem: T)

prim fn printStr(s: Str)
prim fn panic[T: ToStr](msg: T): Void

type Option[T]:
    None
    Some(T)

impl[T] Option[T]:
    fn unwrap(self): T =
        match self:
            Option.None: panic("Unwrapping Option.None")
            Option.Some(value): value

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

impl ToStr for Bool:
    fn toStr(self): Str =
        match self:
            Bool.True: "Bool.True"
            Bool.False: "Bool.False"

trait Iterator[T]:
    type Item

    fn next(self): Option[Item]

trait Step[T]:
    fn next(self): T

fn range[T: Step](start: T, end: T): RangeIterator[T] =
    RangeIterator(current = start, end = end)

fn irange[T: Step](start: T, end: T): InclusiveRangeIterator[T] =
    InclusiveRangeIterator(current = start, end = end)

type RangeIterator[T]:
    current: T
    end: T

impl[T: Step + Ord] Iterator for RangeIterator[T]:
    type Item = T

    fn next(self): Option[T] =
        if self.current >= self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)

type InclusiveRangeIterator[T]:
    current: T
    end: T

impl[T: Step + Ord] Iterator for InclusiveRangeIterator[T]:
    type Item = T

    fn next(self): Option[T] =
        if self.current > self.end:
            Option.None
        else:
            let current = self.current
            self.current = self.current.next()
            Option.Some(current)
