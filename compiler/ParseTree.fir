type ParseTree[t, nt]:
    Terminal(t)

    NonTerminal:
        kind: nt
        nodes: Vec[ParseTree[t, nt]]

type ParseError[t]:
    UnexpectedEof
    UnexpectedToken(t)

impl[ToStr[t]] ToStr[ParseError[t]]:
    toStr(self: ParseError[t]): Str
        match self:
            ParseError.UnexpectedEof: "unexpected end of input"
            ParseError.UnexpectedToken(t): "unexpected token `t`"
