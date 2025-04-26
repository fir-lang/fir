type Result[e, t]:
    Err(e)
    Ok(t)

impl[ToStr[e], ToStr[t]] ToStr[Result[e, t]]:
    toStr(self: Result[e, t]): Str
        match self:
            Result.Err(e): "Result.Err(`e`)"
            Result.Ok(t): "Result.Ok(`t`)"

Result.mapErr(self: Result[e, t], f: Fn(e): e2): Result[e2, t]
    match self:
        Result.Ok(a): Result.Ok(a)
        Result.Err(e): Result.Err(f(e))
