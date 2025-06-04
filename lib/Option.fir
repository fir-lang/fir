type Option[t]:
    None
    Some(t)

impl[ToStr[t]] ToStr[Option[t]]:
    toStr(self: Option[t]) Str:
        match self:
            Option.None: "Option.None"
            Option.Some(t): "Option.Some(`t`)"

impl[Eq[t]] Eq[Option[t]]:
    __eq(self: Option[t], other: Option[t]) Bool:
        match (left = self, right = other):
            (left = Option.None, right = Option.None): Bool.True
            (left = Option.Some(left), right = Option.Some(right)): left == right
            _: Bool.False

Option.map(self: Option[t1], f: Fn(t1) t2 / exn) Option[t2] / exn:
    match self:
        Option.None: Option.None
        Option.Some(val): Option.Some(f(val))

Option.unwrap(self: Option[t]) t:
    match self:
        Option.None: panic("Unwrapping Option.None")
        Option.Some(val): val

Option.unwrapOr(self: Option[t], default: t) t:
    match self:
        Option.None: default
        Option.Some(val): val

Option.unwrapOrElse(self: Option[t], f: Fn() t / exn) t / exn:
    match self:
        Option.None: f()
        Option.Some(val): val

Option.guard(self: Option[t], guard: Fn(t) Bool / exn) Option[t] / exn:
    match self:
        Option.None: Option.None
        Option.Some(val):
            if guard(val):
                Option.Some(val)
            else:
                Option.None

Option.isSome(self: Option[t]) Bool:
    match self:
        Option.Some(_): Bool.True
        Option.None: Bool.False

Option.isNone(self: Option[t]) Bool:
    match self:
        Option.Some(_): Bool.False
        Option.None: Bool.True
