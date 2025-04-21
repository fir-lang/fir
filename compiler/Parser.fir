import Ast
import Error
import Token

type Parser:
    _file: Str

    _tokens: Vec[Token]

    # Index of the next token in `tokens`.
    _idx: U32

Parser.simpleExpr(self): Error Expr
    let token = self._nextToken().unwrapOrElse({
        return self._throwUnexpectedEof()
    })
    match token.kind:
        TokenKind.LowerId:
            self._idx += 1
            Expr.Var(VarExpr(id = self._id(token), tyArgs = Vec.withCapacity(0)))

        TokenKind.UpperId:
            self._idx += 1
            if self._lookaheadKind(0, TokenKind.Dot).isSome():
                self._idx += 1
                match self._nextToken():
                    Option.None:
                        return self._throwUnexpectedEof()
                    Option.Some(next):
                        match next.kind:
                            TokenKind.UpperId:
                                self._idx += 1
                                Expr.ConstrSelect(ConstrSelectExpr(
                                    ty = self._id(token),
                                    constr = self._id(next),
                                    tyArgs = Vec.withCapacity(0)))
                            other:
                                throw(Error(
                                    loc = self._tokenLoc(next),
                                    msg = "unexpected token"))
            else:
                Expr.Constr(ConstrExpr(
                    id = self._id(token),
                    tyArgs = Vec.withCapacity(0)))

        other:
            panic("TODO")

Parser._lookahead(self, amount: U32): Option[Token]
    let idx = self._idx + amount
    if idx >= self._tokens.len():
        return Option.None
    Option.Some(self._tokens.get(idx))

Parser._nextToken(self): Option[Token]
    self._lookahead(0)

Parser._lookaheadKind(self, amount: U32, kind: TokenKind): Option[Token]
    self._lookahead(amount).guard(fn(t) { t.kind == kind })

Parser._tokenLoc(self, token: Token): Loc
    Loc(file = self._file, byteIdx = token.byteIdx, byteLen = token.text.len())

Parser._id(self, token: Token): Id
    Id(name = token.text, idx = 0u32, loc = self._tokenLoc(token))

Parser._throwUnexpectedEof(self): Error a
    throw(Error(
        loc = self._eofLoc(),
        msg = "unexpected end of file"))

Parser._eofLoc(self): Loc
    let byteIdx = self._tokens.last().map(fn(t) { t.byteIdx }).unwrapOr(0u32)
    Loc(file = self._file, byteIdx = byteIdx, byteLen = 0)

parserTest(input: Str, parseFn: Fn(Parser): Error a, astCheck: Fn(a): ())
    let (tokens = tokens, error = error) = tokenize("Test.fir", input)
    error.map(fn(err) { panic(err.msg) })
    
    let parser = Parser(_file = "Test.fir", _tokens = tokens, _idx = 0)
    try({ astCheck(parseFn(parser)) }).unwrapOrElse(fn(err) { panic(err.msg) })
