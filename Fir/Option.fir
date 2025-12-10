#[derive(ToDoc)]
type Option[t]:
    None
    Some(t)


impl[ToDoc[t]] ToDoc[Option[t]]:
    toDoc(self: Option[t]) Doc:
        match self:
            Option.None: Doc.str("Option.None")
            Option.Some(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Option.Some") + Doc.char('(') + args)


impl[ToStr[t]] ToStr[Option[t]]:
    toStr(self: Option[t]) Str:
        match self:
            Option.None: "Option.None"
            Option.Some(t): "Option.Some(`t`)"


impl[Eq[t]] Eq[Option[t]]:
    __eq(self: Option[t], other: Option[t]) Bool:
        match (l = self, r = other):
            (l = Option.None, r = Option.None): Bool.True
            (l = Option.Some(l0), r = Option.Some(r0)): l0 == r0
            _: Bool.False


impl[Eq[t]] Eq[Option[t]]:
    __eq(self: Option[t], other: Option[t]) Bool:
        match (left = self, right = other):
            (left = Option.None, right = Option.None): Bool.True
            (left = Option.Some(left), right = Option.Some(right)):
                left == right
            _: Bool.False


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
