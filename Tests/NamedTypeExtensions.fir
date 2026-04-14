#|
A program demonstrating Fir's named type extension features.

See the blog post for more background on the problem we're trying to solve here:
https://osa1.net/posts/2026-03-07-extensible-named-types-fir.html
|#

# The trait with associated types for each extension in the AST.
#
# Extensions are record rows, so they have explicit kind annotations `Row[Rec]`.
# By default, the kinds are assumed to be "type" (i.e. not row).
trait ExprExts[t]:
    # `Var` node extension.
    type VarExt: Row[Rec]

    # `App` node extension.
    type AppExt: Row[Rec]

    # `Abs` node extension.
    type AbsExt: Row[Rec]

    # `Let` node extension.
    type LetExt: Row[Rec]

    # To be able to generate AST nodes in generic code like the parser, we need
    # default values for the row fields. `(..)` is the record type syntax.
    # `(..row)` makes the `row` (which should be a `Row[Rec]`-kinded type) the
    # row extension of the record. We can also use this syntax with fields, see
    # below.
    defaultVarExt() (..VarExt)

    defaultAppExt() (..AppExt)

    defaultAbsExt() (..AbsExt)

    defaultLetExt() (..LetExt)


# Type synonyms to make it easier to refer to the extension rows.
type VarExt[t] = ExprExts[t].VarExt


type AppExt[t] = ExprExts[t].AppExt


type AbsExt[t] = ExprExts[t].AbsExt


type LetExt[t] = ExprExts[t].LetExt


# The expression type. `exts` is the type parameter for a `ExprExts`
# implementation.
type Expr[exts]:
    Var(
        name: Str,
        ..VarExt[exts]
    )

    App(
        fun: Expr[exts],
        arg: Expr[exts],
        ..AppExt[exts]
    )

    Abs(
        param: Str,
        body: Expr[exts],
        ..AbsExt[exts]
    )

    Let(
        name: Str,
        rhs: Expr[exts],
        body: Expr[exts],
        ..LetExt[exts]
    )


# We can implement traits on this type in a generic way. The `impl` context here
# is a bit verbose because we have to require that each of the extensions
# implement the trait as well.
#
# `RecRowList` is a built-in trait that converts rows to records. Our associated
# types have row kinds, and rows can't implement traits. `RecRowList` turns them
# into records.
impl[
    ToDoc[RecRowList[VarExt[exts]]],
    ToDoc[RecRowList[AppExt[exts]]],
    ToDoc[RecRowList[AbsExt[exts]]],
    ToDoc[RecRowList[LetExt[exts]]],
] ToDoc[Expr[exts]]:
    toDoc(self: Expr[exts]) Doc:
        match self:
            # There's a little bit of novelty here as well, and we'll be
            # inconsistent below to demonstrate features.
            #
            # In a record pattern like `(field1, ..rest)`, `rest` holds a record
            # with the rest of the fields. Since records can implement traits as
            # well, we can just turn all fields into a record and use the
            # record's implementation. (see the end for the output of this)
            #
            # This gives us an easy way to implement many of the traits by just
            # calling the same trait method we're implementing on the records of
            # fields.
            Expr.Var(..fields): Doc.str("Expr.Var") + fields.toDoc()

            # If we, we can handle some of the fields manually and have the rest
            # as a record. Note that `..exts` below includes both the extension
            # fields, and the non-extension `arg` field.
            Expr.App(fun, ..exts):
                Doc.str("Expr.App")
                    + Doc.nested(
                        4,
                        Doc.char('(')
                            + Doc.break_(0)
                            # We use a standard library type to make it easy to format
                            # record fields. This is the same type that the standard
                            # library `ToDoc` implementation for records use.
                            + RecordField(label = "fun", value_ = fun).toDoc()
                            + Doc.char(',')
                            + Doc.break_(1)
                            + exts.toDoc(),
                    )
                    + Doc.break_(0)
                    + Doc.char(')')

            # Match all of the non-extensions, and have the rest in a record.
            Expr.Abs(param, body, ..exts):
                Doc.str("Expr.Abs")
                    + Doc.nested(
                        4,
                        Doc.char('(')
                            + Doc.break_(0)
                            + RecordField(label = "param", value_ = param).toDoc()
                            + Doc.char(',')
                            + Doc.break_(1)
                            + RecordField(label = "body", value_ = body).toDoc()
                            + Doc.char(',')
                            + Doc.break_(1)
                            + exts.toDoc(),
                    )
                    + Doc.break_(0)
                    + Doc.char(')')

            # We've already demonstrated the features, keep it simple for the
            # rest of this.
            Expr.Let(..fields): Doc.str("Expr.Let") + fields.toDoc()


# Type for the formatter's AST extensions.
type FmtExprExts


# Formatter doesn't need any extensions, so all associated types are defined as
# the empty row. Default methods return an empty record.
impl ExprExts[FmtExprExts]:
    type VarExt = row()

    type AppExt = row()

    type AbsExt = row()

    type LetExt = row()

    # There's a limitation in the code below: we can't use `()` as the return
    # types of these methods even though `(..VarExt)` etc. are all `()`s. The
    # reason is because we compare method signatures with trait signatures
    # structurally (after substituting trait type parameters with the impl's
    # arguments), and `()` is not the same as `(..ExprExts[FmtExprExts].VarExt)`
    # structurally. `VarExt` is a synonym for `ExprExts[FmtExprExts].VarExt`, so
    # we can us it.
    #
    # We may be able to improve this in the future and allow `()` as the return
    # types below.
    defaultVarExt() (..VarExt):
        ()

    defaultAppExt() (..AppExt):
        ()

    defaultAbsExt() (..AbsExt):
        ()

    defaultLetExt() (..LetExt):
        ()


# Type for the type checker's AST extensions.
type TcExprExts


# Each expression will be annotated with the inferred types.
impl ExprExts[TcExprExts]:
    type VarExt = row(inferredTy: Option[Ty])

    type AppExt = row(inferredTy: Option[Ty])

    # For functions, we keep argument and return types separately.
    type AbsExt = row(argTy: Option[Ty], retTy: Option[Ty])

    # `Let` expressions keep track of nesting, to be able to generalize.
    type LetExt = row(inferredTy: Option[Ty], level: U32)

    defaultVarExt() (..VarExt):
        (inferredTy = Option.None)

    defaultAppExt() (..AppExt):
        (inferredTy = Option.None)

    defaultAbsExt() (..AbsExt):
        (argTy = Option.None, retTy = Option.None)

    defaultLetExt() (..LetExt):
        # Type inference here is not great, we have to make the type of the
        # integer literal below explicit with the standard library function
        # `u32`, which has the type `Fn(U32) U32`.
        (inferredTy = Option.None, level = u32(0))


# The type-checking types, used in the type checker's AST.
#[derive(ToDoc)]
type Ty:
    Var(Str)
    Arrow(Ty, Ty)


main():
    # The same parser can generate any AST as long as the extension type
    # implements `ExprExts`.

    # Parse as formatter's AST:
    let ast: Expr[FmtExprExts] = Parser.new("(fn x x)").parseExpr()

    # Parse as type checker's AST:
    let ast: Expr[TcExprExts] = Parser.new("(fn x x)").parseExpr()

    # We'll parse and print these programs, as the formatter's and type
    # checker's ASTs.
    let programs = Vec.[
        "x",
        "(fn x x)",
        "(f x)",
        "(let id (fn x x) (id y))",
        "((fn x x) y)",
    ]

    # Parse and print as the formatter's AST:
    for program: Str in programs.iter():
        let parsed: Expr[FmtExprExts] = Parser.new(program).parseExpr()
        print("")
        print(program)
        print(parsed.toDoc().render(80))

    print("-------------")

    # Parse and print as the type checker's AST:
    for program: Str in programs.iter():
        let parsed: Expr[TcExprExts] = Parser.new(program).parseExpr()
        print("")
        print(program)
        print(parsed.toDoc().render(80))


# The parser code is mostly boilerplate. The interesting parts are `Expr`
# allocations, search for `Expr.` below.

#   expr = ident                           # Var
#        | '(' 'fn' ident expr ')'         # Abs
#        | '(' 'let' ident expr expr ')'   # Let
#        | '(' expr expr ')'               # App

type Parser(
    _input: Str,
    _pos: U32,
)


Parser.new(input: Str) Parser:
    Parser(_input = input, _pos = 0)


Parser.atEnd(self) Bool:
    self._pos >= self._input.len()


Parser.peek(self) Option[Char]:
    if self.atEnd():
        Option.None
    else:
        Option.Some(self._input.charAt(self._pos))


Parser.advance(self) Char:
    let c = self._input.charAt(self._pos)
    self._pos += c.lenUtf8()
    c


Parser.skipWhitespace(self):
    while not self.atEnd():
        let c = self._input.charAt(self._pos)
        if c.isAsciiWhitespace():
            self._pos += c.lenUtf8()
        else:
            break


Parser.expectChar(self, expected: Char):
    self.skipWhitespace()
    if self.atEnd():
        panic("unexpected end of input")
    let c = self.advance()
    if c != expected:
        panic("unexpected character")


Parser.parseIdent(self) Str:
    self.skipWhitespace()
    let start = self._pos
    while not self.atEnd():
        let c = self._input.charAt(self._pos)
        if c.isAsciiAlphanumeric() or c == '_':
            self._pos += c.lenUtf8()
        else:
            break
    if self._pos == start:
        panic("expected identifier")
    self._input.substr(start, self._pos)


Parser.parseExpr[ExprExts[exts]](self) Expr[exts]:
    self.skipWhitespace()
    match self.peek():
        Option.None: panic("unexpected end of input")

        Option.Some(c):
            if c == '(':
                self.advance()
                let expr = self.parseSExpr()
                self.expectChar(')')
                expr
            else:
                Expr.Var(
                    name = self.parseIdent(), ..ExprExts[exts].defaultVarExt()
                )


Parser.parseSExpr[ExprExts[exts]](self) Expr[exts]:
    self.skipWhitespace()

    match self.peek():
        Option.None: panic("unexpected end of input")

        Option.Some(c):
            if c.isAsciiAlphanumeric() or c == '_':
                let word = self.parseIdent()
                if word == "fn":
                    let param = self.parseIdent()
                    let body = self.parseExpr()
                    Expr.Abs(param, body, ..ExprExts[exts].defaultAbsExt())
                elif word == "let":
                    let name = self.parseIdent()
                    let rhs = self.parseExpr()
                    let body = self.parseExpr()
                    Expr.Let(name, rhs, body, ..ExprExts[exts].defaultLetExt())
                else:
                    let fun = Expr.Var(
                        name = word, ..ExprExts[exts].defaultVarExt()
                    )
                    let arg = self.parseExpr()
                    Expr.App(fun, arg, ..ExprExts[exts].defaultAppExt())
            else:
                let fun = self.parseExpr()
                let arg = self.parseExpr()
                Expr.App(fun, arg, ..ExprExts[exts].defaultAppExt())


# ------------------------------------------------------------------------------
# Rest of the file is test expectations.

# expected stdout:
# x
# Expr.Var(name = "x")
# 
# (fn x x)
# Expr.Abs(
#     param = "x",
#     body = Expr.Var(name = "x"),
#     ()
# )
# 
# (f x)
# Expr.App(
#     fun = Expr.Var(name = "f"),
#     (arg = Expr.Var(name = "x"))
# )
# 
# (let id (fn x x) (id y))
# Expr.Let(
#     body = Expr.App(
#         fun = Expr.Var(name = "id"),
#         (arg = Expr.Var(name = "y"))
#     ),
#     name = "id",
#     rhs = Expr.Abs(
#         param = "x",
#         body = Expr.Var(name = "x"),
#         ()
#     ),
# )
# 
# ((fn x x) y)
# Expr.App(
#     fun = Expr.Abs(
#         param = "x",
#         body = Expr.Var(name = "x"),
#         ()
#     ),
#     (arg = Expr.Var(name = "y"))
# )
# -------------
# 
# x
# Expr.Var(inferredTy = Option.None, name = "x")
# 
# (fn x x)
# Expr.Abs(
#     param = "x",
#     body = Expr.Var(inferredTy = Option.None, name = "x"),
#     (argTy = Option.None, retTy = Option.None)
# )
# 
# (f x)
# Expr.App(
#     fun = Expr.Var(inferredTy = Option.None, name = "f"),
#     (
#         arg = Expr.Var(inferredTy = Option.None, name = "x"),
#         inferredTy = Option.None,
#     )
# )
# 
# (let id (fn x x) (id y))
# Expr.Let(
#     body = Expr.App(
#         fun = Expr.Var(inferredTy = Option.None, name = "id"),
#         (
#             arg = Expr.Var(inferredTy = Option.None, name = "y"),
#             inferredTy = Option.None,
#         )
#     ),
#     inferredTy = Option.None,
#     level = 0,
#     name = "id",
#     rhs = Expr.Abs(
#         param = "x",
#         body = Expr.Var(inferredTy = Option.None, name = "x"),
#         (argTy = Option.None, retTy = Option.None)
#     ),
# )
# 
# ((fn x x) y)
# Expr.App(
#     fun = Expr.Abs(
#         param = "x",
#         body = Expr.Var(inferredTy = Option.None, name = "x"),
#         (argTy = Option.None, retTy = Option.None)
#     ),
#     (
#         arg = Expr.Var(inferredTy = Option.None, name = "y"),
#         inferredTy = Option.None,
#     )
# )
