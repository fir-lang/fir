#[derive(ToDoc)]
type Result[e, t]:
    Err(e)
    Ok(t)


impl[ToStr[e], ToStr[t]] ToStr[Result[e, t]]:
    toStr(self: Result[e, t]) Str:
        match self:
            Result.Err(e): "Result.Err(`e`)"
            Result.Ok(t): "Result.Ok(`t`)"


impl[Clone[e], Clone[t]] Clone[Result[e, t]]:
    clone(self: Result[e, t]) Result[e, t]:
        match self:
            Result.Err(e): Result.Err(e.clone())
            Result.Ok(t): Result.Ok(t.clone())


Result.map(self: Result[e, t], f: Fn(t) t2 / exn) Result[e, t2] / exn:
    match self:
        Result.Ok(val): Result.Ok(f(val))
        Result.Err(err): Result.Err(err)


Result.mapErr(self: Result[e, t], f: Fn(e) e2 / exn) Result[e2, t] / exn:
    match self:
        Result.Ok(val): Result.Ok(val)
        Result.Err(err): Result.Err(f(err))


Result.unwrap[ToStr[e]](self: Result[e, t]) t:
    match self:
        Result.Ok(val): val
        Result.Err(err): panic(err.toStr())


Result.or_(self: Result[e, t], other: Result[e, t]) Result[e, t]:
    match self:
        Result.Ok(val): Result.Ok(val)
        Result.Err(_): other


Result.orElse(self: Result[e, t], f: Fn() Result[e, t] / exn) Result[e, t] / exn:
    match self:
        Result.Ok(val): Result.Ok(val)
        Result.Err(_): f()


Result.unwrapOr(self: Result[e, t], default: t) t:
    match self:
        Result.Ok(val): val
        Result.Err(_): default


Result.unwrapOrElse(self: Result[e, t], f: Fn(e) t / exn) t / exn:
    match self:
        Result.Ok(val): val
        Result.Err(err): f(err)
