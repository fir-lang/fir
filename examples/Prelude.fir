type Bool:
    False
    True

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
