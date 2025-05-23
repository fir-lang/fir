import Ast
import Error
import Token

type Parser:
    _file: Str

    _tokens: Vec[Token]

    # Index of the next token in `tokens`.
    _idx: U32

Parser.expr(self, prec: U32): Error L[Expr]
    let expr = self.simpleExpr()

    loop:
        let next = match self._nextOpt():
            Option.None: break
            Option.Some(next): next

        let (leftPrec, rightPrec, op) = match _opPrec(next.kind):
            Option.None: break
            Option.Some(prec): prec

        if leftPrec <= prec:
            break

        self._idx += 1
        let right = self.expr(rightPrec)
        let rightLoc = right.loc
        expr = L(
            loc = expr.loc.combine(rightLoc),
            node = Expr.BinOp(BinOpExpr(left = expr, right = right, op = op)),
        )

    expr

Parser.simpleExpr(self): Error L[Expr]
    let token = self._nextOpt().unwrapOrElse({
        return self._throwUnexpectedEof()
    })
    let leftLoc = self._tokenLoc(token)
    match token.kind:
        TokenKind.LowerId:
            self._idx += 1
            L(loc = leftLoc, node = Expr.Var(VarExpr(id = self._id(token), tyArgs = Vec.withCapacity(0))))

        TokenKind.UpperId:
            self._idx += 1
            if self._lookaheadKind(0, TokenKind.Dot).isSome():
                self._idx += 1
                let next = self._next()
                match next.kind:
                    TokenKind.UpperId:
                        let rightLoc = self._tokenLoc(next)
                        self._idx += 1
                        L(
                            loc = leftLoc.combine(rightLoc), node =
                            Expr.ConstrSelect(Constructor(
                                ty = self._id(token),
                                constr = Option.Some(self._id(next)),
                                tyArgs = Vec.withCapacity(0)))
                        )
                    other:
                        throw(Error(
                            loc = self._tokenLoc(next),
                            msg = "unexpected token"))
            else:
                L(
                    loc = leftLoc,
                    node = Expr.ConstrSelect(Constructor(
                        ty = self._id(token),
                        constr = Option.None,
                        tyArgs = Vec.withCapacity(0)))
                )

        TokenKind.Int(kind):
            self._idx += 1
            L(
                loc = leftLoc,
                node = Expr.Int(IntExpr(
                    text = token.text,
                    suffix = kind,
                    radix = 10,

                    # Type checker will update this based on `suffix`, or the inferred type if suffix is
                    # not available.
                    parsed = 0,
                ))
            )

        TokenKind.HexInt(kind):
            self._idx += 1
            L(
                loc = leftLoc,
                node = Expr.Int(IntExpr(
                    text = token.text,
                    suffix = kind,
                    radix = 16,
                    parsed = 0,  # same as above
                ))
            )

        TokenKind.BinInt(kind):
            self._idx += 1
            L(
                loc = leftLoc,
                node = Expr.Int(IntExpr(
                    text = token.text,
                    suffix = kind,
                    radix = 2,
                    parsed = 0,  # same as above
                ))
            )

        TokenKind.Str:
            self._idx += 1
            # TODO: Parse parts
            let parts: Vec[StrPart] = Vec.withCapacity(1)
            parts.push(StrPart.Str(token.text))
            L(loc = leftLoc, node = Expr.Str(parts))

        TokenKind.Char:
            self._idx += 1
            L(loc = leftLoc, node = Expr.Char(_parseChar(token.text)))

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

# TODO: Tweak left and right precedences based on associativity.
_opPrec(token: TokenKind): Option[(leftPrec: U32, rightPrec: U32, op: BinOp)]
    match token:
        TokenKind.Star:
            Option.Some((leftPrec = 11, rightPrec = 11, op = BinOp.Multiply))

        TokenKind.Slash:
            Option.Some((leftPrec = 11, rightPrec = 11, op = BinOp.Divide))

        TokenKind.Plus:
            Option.Some((leftPrec = 10, rightPrec = 10, op = BinOp.Add))

        TokenKind.Minus:
            Option.Some((leftPrec = 10, rightPrec = 10, op = BinOp.Subtract))

        TokenKind.DoubleLAngle:
            Option.Some((leftPrec = 9, rightPrec = 9, op = BinOp.LeftShift))

        TokenKind.DoubleRAngle:
            Option.Some((leftPrec = 9, rightPrec = 9, op = BinOp.RightShift))

        TokenKind.Amp:
            Option.Some((leftPrec = 8, rightPrec = 8, op = BinOp.BitAnd))

        TokenKind.Pipe:
            Option.Some((leftPrec = 7, rightPrec = 7, op = BinOp.BitAnd))

        TokenKind.EqEq:
            Option.Some((leftPrec = 6, rightPrec = 6, op = BinOp.Equal))

        TokenKind.ExclamationEq:
            Option.Some((leftPrec = 6, rightPrec = 6, op = BinOp.NotEqual))

        TokenKind.LAngle:
            Option.Some((leftPrec = 6, rightPrec = 6, op = BinOp.Lt))

        TokenKind.RAngle:
            Option.Some((leftPrec = 6, rightPrec = 6, op = BinOp.Gt))

        TokenKind.LAngleEq:
            Option.Some((leftPrec = 6, rightPrec = 6, op = BinOp.LtEq))

        TokenKind.RAngleEq:
            Option.Some((leftPrec = 6, rightPrec = 6, op = BinOp.GtEq))

        TokenKind.AmpAmp:
            Option.Some((leftPrec = 5, rightPrec = 5, op = BinOp.And))

        TokenKind.PipePipe:
            Option.Some((leftPrec = 4, rightPrec = 4, op = BinOp.Or))

        _: Option.None

# --------------------------------------------------------------------------------------------------
# Type declarations

Parser.typeDecl(self): Error L[TypeDecl]
    let typeToken = self._next()

    if !(typeToken is Token(kind = TokenKind.Type, ..)):
        throw(Error(loc = self._tokenLoc(typeToken), msg = "unexpected token"))

    self._idx += 1

    let nameToken = self._expect(TokenKind.UpperId)

    let name = nameToken.text

    let next = self._next()
    self._idx += 1

    let typeParams: Vec[Id] = Vec.withCapacity(0)

    if next.kind is TokenKind.LBracket:
        loop:
            let next = self._next()
            self._idx += 1

            match next.kind:
                TokenKind.LowerId: typeParams.push(self._id(next))
                _: throw(Error(loc = self._tokenLoc(next), msg = "expected type parameter"))

            next = self._next()
            self._idx += 1

            match next.kind:
                TokenKind.Comma: ()
                TokenKind.RBracket: break
                _: throw(Error(loc = self._tokenLoc(next), msg = "expected ',' or ']'"))

            next = self._next()
            if next.kind is TokenKind.RBracket:
                self._idx += 1
                break

            # Otherwise continue with the next type param.

    if !(self._next().kind is TokenKind.Colon):
        return L(
            loc = self._tokenLoc(typeToken).combine(self._tokenLoc(next)),
            node = TypeDecl(
                name = self._id(nameToken),
                typeParams,
                typeParamKinds = Vec.withCapacity(typeParams.len()),
                rhs = Option.None))

    self._idx += 1

    self._expect(TokenKind.Newline)
    self._expect(TokenKind.Indent)

    let rhs: TypeDeclRhs = match self._next().kind:
        TokenKind.UpperId:
            let alts: Vec[ConstructorDecl] = Vec.withCapacity(10)

            loop:
                alts.push(self.constructorDecl())
                self._expect(TokenKind.Newline)
                if self._next().kind is TokenKind.Dedent:
                    self._idx += 1
                    break

            TypeDeclRhs.Sum(alts)

        TokenKind.LowerId:
            let fields = self.constructorFields()
            self._expect(TokenKind.Newline)
            TypeDeclRhs.Product(fields)

        other: throw(Error(loc = self._tokenLoc(next), msg = "expected upper or lower id"))

    L(
        loc = self._tokenLoc(typeToken).combine(self._tokenLoc(next)),
        node = TypeDecl(
            name = self._id(nameToken),
            typeParams,
            typeParamKinds = Vec.withCapacity(typeParams.len()),
            rhs = Option.Some(rhs)))

Parser.constructorDecl(self): Error ConstructorDecl
    let conName = self._expect(TokenKind.UpperId)
    let fields = self.constructorFields()
    ConstructorDecl(name = self._id(conName), fields)

Parser.constructorFields(self): Error ConstructorFields
    match self._next().kind:
        TokenKind.Colon:
            self._idx += 1
            self._expect(TokenKind.Newline)
            self._expect(TokenKind.Indent)
            let fields: Vec[(name: Id, ty: L[Type])] = Vec.withCapacity(5)
            loop:
                let fieldId = self._expect(TokenKind.LowerId)
                self._expect(TokenKind.Colon)
                let ty = self.ltype()
                fields.push((name = self._id(fieldId), ty = ty))
                self._expect(TokenKind.Newline)
                if self._next().kind is TokenKind.Dedent:
                    self._idx += 1
                    break
            return ConstructorFields.Named(fields)

        TokenKind.LParen:
            panic("TODO")

        TokenKind.Newline:
            ConstructorFields.Empty

        other: throw(Error(
            loc = self._eofLoc(),
            msg = "unexpected end of file"))

# --------------------------------------------------------------------------------------------------
# Types

Parser.ltype(self): Error L[Type]
    let first = self._next()
    self._idx += 1

    match first.kind:
        TokenKind.UpperId:
            let lastToken = first

            let args: Vec[L[Type]] = Vec.withCapacity(0)

            if self._nextOpt() is Option.Some(Token(kind = TokenKind.LBracket, ..)):
                self._idx += 1

                let expectBracket = Bool.False

                loop:
                    let typeToken = self._next()

                    if typeToken.kind is TokenKind.RBracket:
                        self._idx += 1
                        lastToken = typeToken
                        break

                    args.push(self.ltype())

                    if self._next().kind is TokenKind.Comma:
                        self._idx += 1
                    elif self._next().kind is TokenKind.RBracket:
                        break
                    else:
                        throw(Error(
                            loc = self._tokenLoc(self._next()),
                            msg = "expected ',' or ']'"))

                if expectBracket:
                    self._expect(TokenKind.RBracket)

            L(node = Type.Named(NamedType(name = self._id(first), args)),
                loc = self._tokenLoc(first).combine(self._tokenLoc(lastToken)))

        TokenKind.LowerId:
            L(node = Type.Var(self._id(first)), loc = self._tokenLoc(first))

        TokenKind.LParen:
            let fields: Vec[Named[L[Type]]] = Vec.withCapacity(5)
            let extension: Option[Id] = Option.None
            let lastToken = first
            let sawComma = Bool.False

            loop:
                # We're starting parsing, or we saw a ','.
                let fieldToken = self._next()

                if fieldToken.kind is TokenKind.RParen:
                    self._idx += 1
                    lastToken = fieldToken
                    break

                if sawComma && fieldToken.kind is TokenKind.DotDot:
                    self._idx += 1
                    let extensionName = self._expect(TokenKind.LowerId)
                    extension = Option.Some(self._id(extensionName))
                    lastToken = fieldToken
                    break

                let name: Option[Id] = Option.None

                # Lower id could be a type variable or field name. Field name will be followed by
                # '='.
                if fieldToken.kind is TokenKind.LowerId:
                    self._idx += 1
                    if self._next().kind is TokenKind.Colon:
                        name = Option.Some(self._id(fieldToken))
                        self._idx += 1
                    else:
                        # Rewind to parse lower id as type variable.
                        self._idx -= 1

                let ty = self.ltype()
                fields.push(Named(name, node = ty))

                if self._next().kind is TokenKind.Comma:
                    sawComma = Bool.True
                    self._idx += 1
                else:
                    sawComma = Bool.False

            L(node = Type.Record(fields, extension),
                loc = self._tokenLoc(first).combine(self._tokenLoc(lastToken)))

        TokenKind.LBracket:
            let alts: Vec[VariantAlt] = Vec.withCapacity(5)
            let extension: Option[Id] = Option.None
            let lastToken = first
            let sawComma = Bool.False

            loop:
                # We're starting parsing, or we saw a ','.
                let altToken = self._next()

                if altToken.kind is TokenKind.RBracket:
                    self._idx += 1
                    lastToken = altToken
                    break

                if sawComma && altToken.kind is TokenKind.DotDot:
                    self._idx += 1
                    let extensionName = self._expect(TokenKind.LowerId)
                    extension = Option.Some(self._id(extensionName))
                    lastToken = altToken
                    break

                let name = self._expect(TokenKind.UpperId)

                panic("TODO")
            panic("TODO")

        TokenKind.Fn_: panic("TODO")

        other: throw(Error(
            loc = self._tokenLoc(first),
            msg = "expected upper or lower id, '(', '[', 'fn'"))

# --------------------------------------------------------------------------------------------------
# Utilities and helpers

Parser._expect(self, expected: TokenKind): Error Token
    let next = self._next()
    self._idx += 1
    if next.kind != expected:
        throw(Error(loc = self._tokenLoc(next), msg = "expected `expected`"))
    next

Parser._lookahead(self, amount: U32): Option[Token]
    let idx = self._idx + amount
    if idx >= self._tokens.len():
        return Option.None
    Option.Some(self._tokens.get(idx))

Parser._nextOpt(self): Option[Token]
    self._lookahead(0)

Parser._next(self): Error Token
    match self._lookahead(0):
        Option.Some(token): token
        Option.None: self._throwUnexpectedEof()

Parser._lookaheadKind(self, amount: U32, kind: TokenKind): Option[Token]
    self._lookahead(amount).guard(fn(t) { t.kind == kind })

Parser._tokenLoc(self, token: Token): Loc
    Loc(file = self._file, byteIdx = token.byteIdx, byteLen = token.text.len(), line = token.line, col = token.col)

Parser._id(self, token: Token): Id
    Id(name = token.text, idx = 0, loc = self._tokenLoc(token))

Parser._throwUnexpectedEof(self): Error a
    throw(Error(
        loc = self._eofLoc(),
        msg = "unexpected end of file"))

Parser._eofLoc(self): Loc
    let byteIdx = self._tokens.last().map(fn(t) { t.byteIdx }).unwrapOr(0)
    Loc(file = self._file, byteIdx = byteIdx, byteLen = 0, line = 0, col = 0)

# --------------------------------------------------------------------------------------------------

parserTests
    _parserTest(
        "simpleExpr - parse failure test (expected to fail)",
        "~~~",
        Parser.simpleExpr,
        fn(ast) { () })

    _parserTest(
        "simpleExpr - assertion failure test (expected to fail)",
        "1u32",
        Parser.simpleExpr,
        fn(ast) { assertEq(1u32, 2u32) })

    _parserTest("simpleExpr - Constr", "A", Parser.simpleExpr, fn(ast) {
        match ast.node:
            Expr.ConstrSelect(constr): assertEq("A", constr.ty.name)
            _: throw(~AssertionError(msg = "Expected constr"))
    })

    _parserTest("simpleExpr - ConstrSelect", "A.B", Parser.simpleExpr, fn(ast) {
        match ast.node:
            Expr.ConstrSelect(constr):
                assertEq("A", constr.ty.name)
                assertEq("B", constr.constr.unwrap().name)
            _:
                throw(~AssertionError(msg = "Expected constr selection"))
    })

    _parserTest("simpleExpr - Int decimal", "123u32", Parser.simpleExpr, fn(ast) {
        match ast.node:
            Expr.Int(int): assertEq("123u32", int.text)
            _: throw(~AssertionError(msg = "Expected int"))
    })

    _parserTest("simpleExpr - Char simple", "'a'", Parser.simpleExpr, fn(ast) {
        match ast.node:
            Expr.Char('a'): ()
            _: throw(~AssertionError(msg = "Expected int"))
    })

    _parserTest("simpleExpr - Char escape newline", "'\\n'", Parser.simpleExpr, fn(ast) {
        match ast.node:
            Expr.Char('\n'): ()
            _: throw(~AssertionError(msg = "Expected int"))
    })

    _parserTest("simpleExpr - Char escape single quote", "'\\''", Parser.simpleExpr, fn(ast) {
        match ast.node:
            Expr.Char('\''): ()
            _: throw(~AssertionError(msg = "Expected int"))
    })

    _parserTest("expr - binop +", "1 + 2", fn(s) { Parser.expr(s, 0) }, fn(ast) {
        match ast.node:
            Expr.BinOp(BinOpExpr(
                left  = L(node = Expr.Int(IntExpr(text = "1", ..)), ..),
                right = L(node = Expr.Int(IntExpr(text = "2", ..)), ..),
                op    = BinOp.Add
            )): ()
            _: throw(~AssertionError(msg = "Expected binop"))
    })

    _parserTest("type - named wo args", "Foo", Parser.ltype, fn(ast) {
        match ast.node:
            Type.Named(NamedType(name, args)):
                assertEq("Foo", name.name)
                assertEq(0u32, args.len())
            other: throw(~AssertionError(msg = "Expected named type wo args, found `other.pprint().print(80)`"))
    })

    _parserTest("type - named w args", "Foo[A, b]", Parser.ltype, fn(ast) {
        match ast.node:
            Type.Named(NamedType(name, args)):
                assertEq("Foo", name.name)
                assertEq(2u32, args.len())
                # BUG TODO: Enabling both of these lines causes an interpreter panic. Enabling only
                # one works.
                # assert(args.get(0).node is Type.Named(NamedType(args, ..)) && args.len() == 0, "Wrong first arg")
                # assert(args.get(1).node is Type.Var(_), "Wrong second arg")
            other: throw(~AssertionError(msg = "Expected named type args, found `other.pprint().print(80)`"))
    })

    _parserTest("type - variable", "foo", Parser.ltype, fn(ast) {
        match ast.node:
            Type.Var(var_): assertEq("foo", var_.name)
            other: throw(~AssertionError(msg = "Expected type variable, found `other.pprint().print(80)`"))
    })

    _parserTest("type - record wo names", "(U32, a)", Parser.ltype, fn(ast) {
        match ast.node:
            Type.Record(fields, extension):
                assertEq(2u32, fields.len())
                assert(extension is Option.None, "Unexpected extension")
                assert(
                    fields.iter().all(fn(field: Named[L[Type]]): Bool { field.name is Option.None }),
                    "Field with name")
            other: throw(~AssertionError(msg = "Unexpected type: `other.pprint().print(80)`"))
    })

    _parserTest("type - record w names", "(x: U32, y: a)", Parser.ltype, fn(ast) {
        match ast.node:
            Type.Record(fields, extension):
                assertEq(2u32, fields.len())
                assert(extension is Option.None, "Unexpected extension")
                assert(
                    fields.iter().all(fn(field: Named[L[Type]]): Bool { field.name is Option.Some(_) }),
                    "Field without name")
            other: throw(~AssertionError(msg = "Unexpected type: `other.pprint().print(80)`"))
    })

_parserTest( \
        testName: Str, input: Str, \
        parseFn: Fn(Parser): Error a, \
        astCheck: Fn(a): [AssertionError(msg: Str)] ())
    printNoNl(testName)
    let (tokens, error) = tokenize("Test.fir", input)
    if error is Option.Some(error):
        print("\t\tLexer error: `error.msg`")
        return

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
