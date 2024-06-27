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
