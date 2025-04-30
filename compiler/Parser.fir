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

        TokenKind.Int(kind):
            Expr.Int(IntExpr(
                text = token.text,
                suffix = kind,
                radix = 10,

                # Type checker will update this based on `suffix`, or the inferred type if suffix is
                # not available.
                parsed = 0u32,
            ))

        TokenKind.HexInt(kind):
            Expr.Int(IntExpr(
                text = token.text,
                suffix = kind,
                radix = 16,
                parsed = 0u32,  # same as above
            ))

        TokenKind.BinInt(kind):
            Expr.Int(IntExpr(
                text = token.text,
                suffix = kind,
                radix = 2,
                parsed = 0u32,  # same as above
            ))

        TokenKind.Str:
            # TODO: Parse parts
            let parts: Vec[StrPart] = Vec.withCapacity(1)
            parts.push(StrPart.Str(token.text))
            Expr.Str(parts)

        TokenKind.Char:
            Expr.Char(_parseChar(token.text))

        other:
            throw(Error(
                loc = self._tokenLoc(token),
                msg = "unexpected token"))

_parseChar(charTest: Str): Char
    let chars = charTest.chars()
    let _: Option[Char] = chars.next() # skip initial '
    match chars.next():
        Option.Some('\\'):
            match chars.next():
                Option.Some('n'): '\n'
                Option.Some('t'): '\t'
                Option.Some('r'): '\r'
                Option.Some('\\'): '\\'
                Option.Some('\''): '\''
                other: panic("Strange char character after opening quote: `other`")
        Option.Some(other): other
        Option.None: panic("Unterminated char literal")

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

# --------------------------------------------------------------------------------------------------

_parserTest( \
        name: Str, input: Str, \
        parseFn: Fn(Parser): Error a, \
        astCheck: Fn(a): [AssertionError(msg: Str)] ())
    printNoNl(name)
    let (tokens = tokens, error = error) = tokenize("Test.fir", input)
    match error:
        Option.Some(err):
            print("\t\tLexer error: `err.msg`")
            return
        Option.None:
            ()

    let parser = Parser(_file = "Test.fir", _tokens = tokens, _idx = 0)

    let ast = match try({ parseFn(parser) }):
        Result.Err(err):
            print("\t\tParser error: `err.msg`")
            return
        Result.Ok(ast):
            ast

    match try({ astCheck(ast) }):
        Result.Ok(()): print("\t\tOK")
        Result.Err(~AssertionError(msg = msg)): print("\t\tAssertion error: `msg`")

parserTests
    _parserTest(
        "simpleExpr -- parse failure test",
        "~~~",
        Parser.simpleExpr,
        fn(ast) { () })

    _parserTest(
        "simpleExpr -- assertion failure test",
        "1u32",
        Parser.simpleExpr,
        fn(ast) { assertEq(1u32, 2u32) })

    _parserTest("simpleExpr - Constr", "A", Parser.simpleExpr, fn(ast) {
        match ast:
            Expr.Constr(constr): assertEq("A", constr.id.name)
            _: throw(~AssertionError(msg = "Expected constr"))
    })

    _parserTest("simpleExpr - ConstrSelect", "A.B", Parser.simpleExpr, fn(ast) {
        match ast:
            Expr.ConstrSelect(constr):
                assertEq("A", constr.ty.name)
                assertEq("B", constr.constr.name)
            _:
                throw(~AssertionError(msg = "Expected constr selection"))
    })

    _parserTest("simpleExpr - Int decimal", "123u32", Parser.simpleExpr, fn(ast) {
        match ast:
            Expr.Int(int): assertEq("123u32", int.text)
            _: throw(~AssertionError(msg = "Expected int"))
    })

    _parserTest("simpleExpr - Char simple", "'a'", Parser.simpleExpr, fn(ast) {
        match ast:
            Expr.Char('a'): ()
            _: throw(~AssertionError(msg = "Expected int"))
    })

    _parserTest("simpleExpr - Char escape newline", "'\\n'", Parser.simpleExpr, fn(ast) {
        match ast:
            Expr.Char('\n'): ()
            _: throw(~AssertionError(msg = "Expected int"))
    })

    _parserTest("simpleExpr - Char escape single quote", "'\\''", Parser.simpleExpr, fn(ast) {
        match ast:
            Expr.Char('\''): ()
            _: throw(~AssertionError(msg = "Expected int"))
    })
