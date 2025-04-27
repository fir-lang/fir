type Result[e, t]:
    Err(e)
    Ok(t)

impl[ToStr[e], ToStr[t]] ToStr[Result[e, t]]:
    toStr(self: Result[e, t]): Str
        match self:
            Result.Err(e): "Result.Err(`e`)"
            Result.Ok(t): "Result.Ok(`t`)"

Result.map(self: Result[e, t], f: Fn(t): exn t2): exn Result[e, t2]
    match self:
        Result.Ok(val): Result.Ok(f(val))
        Result.Err(err): Result.Err(err)

Result.mapErr(self: Result[e, t], f: Fn(e): exn e2): exn Result[e2, t]
    match self:
        Result.Ok(val): Result.Ok(val)
        Result.Err(err): Result.Err(f(err))

Result.unwrap[ToStr[e]](self: Result[e, t]): t
    match self:
        Result.Ok(val): val
        Result.Err(err): panic(err.toStr())

Result.unwrapOr(self: Result[e, t], default: t): t
    match self:
        Result.Ok(val): val
        Result.Err(_): default

Result.unwrapOrElse(self: Result[e, t], f: Fn(e): exn t): exn t
    match self:
        Result.Ok(val): val
        Result.Err(err): f(err)

Result.isOk(self: Result[e, t]): Bool
    match self:
        Result.Ok(_): Bool.True
        Result.Err(_): Bool.False

Result.isErr(self: Result[e, t]): Bool
    match self:
        Result.Ok(_): Bool.False
        Result.Err(_): Bool.True
