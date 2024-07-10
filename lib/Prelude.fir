prim type Str

prim fn Str.__eq(self, other: Str): Bool
prim fn Str.len(self): I32
prim fn Str.substr(self, byteStart: I32, byteEnd: I32): StrView

prim type StrView

prim fn StrView.__eq(self, other: StrView): Bool
prim fn StrView.isEmpty(self): Bool
prim fn StrView.len(self): I32
prim fn StrView.startsWith(self, str: Str): Bool
prim fn StrView.substr(self, byteStart: I32, byteEnd: I32): StrView
prim fn StrView.toStr(self): Str

prim type I32

prim fn I32.__add(self, other: I32): I32
prim fn I32.__cmp(self, other: I32): Ordering
prim fn I32.__eq(self, other: I32): Bool
prim fn I32.__mul(self, other: I32): I32
prim fn I32.__sub(self, other: I32): I32
prim fn I32.toStr(self): Str

prim type Array[T]

prim fn Array.new(len: I32): Array[T]
prim fn Array.len(self): I32
prim fn Array.get(self, idx: I32): T
prim fn Array.set(self, idx: I32, elem: T)

prim fn printStr(s: Str)
prim fn printStrView(s: StrView)
prim fn panic(message: StrView)

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

fn Bool.__and(self, other: Bool): Bool =
    match self:
        Bool.False: Bool.False
        Bool.True: other

fn Bool.__or(self, other: Bool): Bool =
    match self:
        Bool.True: Bool.True
        Bool.False: other

fn Bool.toStr(self): Str =
    match self:
        Bool.True: "Bool.True"
        Bool.False: "Bool.False"

# TODO: We may want to allow unnamed fields: `type Char(U32)`.
type Char:
    value: I32 # TODO: Switch to U32 when we have it.

fn Char.__eq(self, other: Char): Bool =
    self.value == other.value
