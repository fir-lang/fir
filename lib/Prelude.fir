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
