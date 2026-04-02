#[derive(ToDoc, Eq)]
value type Option[t]:
    None
    Some(t)


impl[ToStr[t]] ToStr[Option[t]]:
    toStr(self: Option[t]) Str:
        match self:
            Option.None: "Option.None"
            Option.Some(t): "Option.Some(`t`)"


impl[Clone[t]] Clone[Option[t]]:
    clone(self: Option[t]) Option[t]:
        match self:
            Option.None: Option.None
            Option.Some(t): Option.Some(t.clone())


Option.map(self: Option[t1], f: Fn(t1) t2 / exn) Option[t2] / exn:
    match self:
        Option.None: Option.None
        Option.Some(val): Option.Some(f(val))


Option.unwrap(self: Option[t]) t:
    match self:
        Option.None: panic("Unwrapping Option.None")
        Option.Some(val): val


Option.or_(self: Option[t], other: Option[t]) Option[t]:
    match self:
        Option.Some(val): Option.Some(val)
        Option.None: other


Option.orElse(self: Option[t], f: Fn() Option[t] / exn) Option[t] / exn:
    match self:
        Option.Some(val): Option.Some(val)
        Option.None: f()


Option.unwrapOr(self: Option[t], default: t) t:
    match self:
        Option.None: default
        Option.Some(val): val


Option.unwrapOrElse(self: Option[t], f: Fn() t / exn) t / exn:
    match self:
        Option.None: f()
        Option.Some(val): val


Option.guard(self: Option[t], guard: Fn(t) Bool / exn) Option[t] / exn:
    if self is Option.Some(val) and guard(val):
        return Option.Some(val)
    Option.None


Option.flatten(self: Option[Option[t]]) Option[t]:
    match self:
        Option.Some(Option.Some(a)): Option.Some(a)
        _: Option.None
