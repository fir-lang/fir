#[derive(ToDoc)]
type Result[e, t]:
    Err(e)
    Ok(t)


impl[ToDoc[e], ToDoc[t]] ToDoc[Result[e, t]]:
    toDoc(self: Result[e, t]) Doc:
        match self:
            Result.Err(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Result.Err") + Doc.char('(') + args)
            Result.Ok(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Result.Ok") + Doc.char('(') + args)


impl[ToStr[e], ToStr[t]] ToStr[Result[e, t]]:
    toStr(self: Result[e, t]) Str:
        match self:
            Result.Err(e): "Result.Err(`e`)"
            Result.Ok(t): "Result.Ok(`t`)"


impl[Eq[e], Eq[t]] Eq[Result[e, t]]:
    __eq(self: Result[e, t], other: Result[e, t]) Bool:
        match (l = self, r = other):
            (l = Result.Err(l0), r = Result.Err(r0)): l0 == r0
            (l = Result.Ok(l0), r = Result.Ok(r0)): l0 == r0
            _: Bool.False


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


Result.unwrapOr(self: Result[e, t], default: t) t:
    match self:
        Result.Ok(val): val
        Result.Err(_): default


Result.unwrapOrElse(self: Result[e, t], f: Fn(e) t / exn) t / exn:
    match self:
        Result.Ok(val): val
        Result.Err(err): f(err)
