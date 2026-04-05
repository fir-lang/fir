import [
    Compiler/Assert,
    Compiler/Token,
]


## Associated types for identifiers in the ASTs.
trait AstIds[t]:
    ## Identifiers that refer to terms.
    type AstVarId

    ## Identifiers that refer to types.
    type AstTyId

    ## Identifiers that refer to associated variables.
    type AstAssocVarId

    ## For parsing: create an `AstVarId` from a token.
    astVarIdFromToken(token: TokenIdx) AstVarId

    ## For parsing: create an `AstTyId` from a token.
    astTyIdFromToken(token: TokenIdx) AstTyId

    ## For parsing: create an `AstAssocVarId` from a token.
    astAssocVarIdFromToken(token: TokenIdx) AstAssocVarId


trait AstExts[t]:
    ## Identifier types used in the AST. This should be an implementation of
    ## `AstIds`.
    type Ids

    ## Extensions for type declarations. (`TypeDecl`)
    type TypeDeclExts: Row[Rec] = row()

    ## Extensions for trait declarations. (`TraitDecl`)
    type TraitDeclExts: Row[Rec] = row()

    ## Extensions for impl declarations. (`ImplDecl`)
    type ImplDeclExts: Row[Rec] = row()

    ## Extensions for function signatures. (`FunSig`)
    type FunSigExts: Row[Rec] = row()

    ## Extensions for record patterns. (`RecordPat`)
    type RecordPatExts: Row[Rec] = row()

    ## Extensions for variant patterns. (`VariantPat`)
    type VariantPatExts: Row[Rec] = row()

    ## Extensions for type argument lists. (`TyArgs`)
    type TyArgsExts: Row[Rec] = row()

    ## Used in expressions with non-trivial types: inferred type fields.
    type InferredTyExts: Row[Rec] = row()

    ## For constructing an AST: default values for the `TypeDeclExts` extension.
    defaultTypeDeclExts() (..TypeDeclExts):
        ()

    ## For constructing an AST: default values for the `TraitDeclExts` extension.
    defaultTraitDeclExts() (..TraitDeclExts):
        ()

    ## For constructing an AST: default values for the `ImplDeclExts` extension.
    defaultImplDeclExts() (..ImplDeclExts):
        ()

    ## For constructing an AST: default values for the `FunSigExts` extension.
    defaultFunSigExts() (..FunSigExts):
        ()

    ## For constructing an AST: default values for the `RecordPatExts` extension.
    defaultRecordPatExts() (..RecordPatExts):
        ()

    ## For constructing an AST: default values for the `VariantPatExts` extension.
    defaultVariantPatExts() (..VariantPatExts):
        ()

    ## For constructing an AST: default values for the `TyArgsExts` extension.
    defaultTyArgsExts() (..TyArgsExts):
        ()

    ## For constructing an AST: default values for the `InferredTyExts` extension.
    defaultInferredTyExts() (..InferredTyExts):
        ()


## Type synonym to make it easy to access `AstIds.AstTyId` from an `AstExts`.
type AstTyId[exts] = AstIds[AstExts[exts].Ids].AstTyId


## Type synonym to make it easy to access `AstIds.AstVarId` from an `AstExts`.
type AstVarId[exts] = AstIds[AstExts[exts].Ids].AstVarId


## Type synonym to make it easy to access `AstIds.AstAssocVarId` from an `AstExts`.
type AstAssocVarId[exts] = AstIds[AstExts[exts].Ids].AstAssocVarId


type DefaultAstExts


impl ToDoc[DefaultAstExts]:
    toDoc(self: DefaultAstExts) Doc:
        panic("unreachable")


type DefaultIds


impl AstExts[DefaultAstExts]:
    type Ids = DefaultIds


impl AstIds[DefaultIds]:
    type AstVarId = Id

    type AstTyId = Id

    type AstAssocVarId = Id

    astVarIdFromToken(token: TokenIdx) AstVarId:
        Id(token)

    astTyIdFromToken(token: TokenIdx) AstTyId:
        Id(token)

    astAssocVarIdFromToken(token: TokenIdx) AstAssocVarId:
        Id(token)


trait Tokens[t]:
    firstToken(self: t, tokens: Array[Token]) TokenIdx

    lastToken(self: t, tokens: Array[Token]) TokenIdx


#[derive(ToDoc)]
value type Id(
    token: TokenIdx,
)


impl Tokens[Id]:
    firstToken(self: Id, tokens: Array[Token]) TokenIdx:
        self.token

    lastToken(self: Id, tokens: Array[Token]) TokenIdx:
        self.token


## A top-level declaration.
#[derive(ToDoc)]
type TopDecl[exts]:
    ## A type declaration: `type T: ...`.
    Type(TypeDecl[exts])

    ## A function declaration: `f(...) = ...`.
    Fun(FunDecl[exts])

    ## An import declaration.
    Import(ImportDecl)

    ## A trait declaration.
    Trait(TraitDecl[exts])

    ## An `impl` block, implementing a trait or associated methods for a type.
    Impl(ImplDecl[exts])


## A type declaration: `type Vec[t](...)`, `value type Bool: ...`.
#[derive(ToDoc)]
type TypeDecl[exts](
    ## Attributes of the type: e.g. `#[derive(ToDoc, Eq)]`.
    attr: Option[Attribute[exts]],

    ## The `value` token in value type declarations: `value type Bool: ...`.
    ##
    ## A type can't be both `value` and `prim`, the parser only allows one of them.
    value_: Option[TokenIdx],

    ## The `prim` token in built-in type declarations: `prim type U32`.
    ##
    ## A type can't be both `value` and `prim`, the parser only allows one of them.
    prim_: Option[TokenIdx],

    ## The type name. `Vec` in the example.
    name: Id,

    ## Constructors of the type.
    rhs: Option[TypeDeclRhs[exts]],

    ## Type parameters of the type. `[t]` in the example.
    typeParams: Vec[DeclTypeParam[exts]],
    ..AstExts[exts].TypeDeclExts
)


impl Tokens[TypeDecl[exts]]:
    firstToken(self: TypeDecl[exts], tokens: Array[Token]) TokenIdx:
        self.value_.or_(self.prim_).unwrapOr(self.name.token)

    lastToken(self: TypeDecl[exts], tokens: Array[Token]) TokenIdx:
        panic("TOOD")


## Constructors of a type declaration.
#[derive(ToDoc)]
type TypeDeclRhs[exts]:
    ## A sum type, with more than one constructor.
    Sum(
        cons: Vec[ConDecl[exts]],
        extension: Option[Type[exts]],
    )

    ## A product type uses the type name as the constructor and only has fields.
    Product(ConFields[exts])

    ## A type synonym: `type Foo = U32`
    Synonym(Type[exts])


## A sum type constructor.
#[derive(ToDoc)]
type ConDecl[exts](
    name: Id,
    fields: ConFields[exts],
    _lastToken: TokenIdx,
)


impl Tokens[ConDecl[exts]]:
    firstToken(self: ConDecl[exts], tokens: Array[Token]) TokenIdx:
        self.name.token

    lastToken(self: ConDecl[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type ConFields[exts]:
    Empty
    Named(
        fields: Vec[NamedField[exts]],
        extension: Option[Type[exts]],
    )
    Unnamed(Vec[Type[exts]])


#[derive(ToDoc)]
type NamedField[exts](
    name: Id,
    ty: Type[exts],
)


#[derive(ToDoc)]
type FunDecl[exts](
    ## When the function is a primitive, the `prim` token.
    prim_: Option[TokenIdx],

    ## Only in associated functions: the parent type. E.g. `Vec` in `Vec.push(...): ...`.
    parentTy: Option[AstTyId[exts]],

    ## Name of the function.
    name: Id,

    ## Type signature of the function.
    sig: FunSig[exts],

    ## Body (code) of the function. Not available in `prim` functions.
    body: Option[Vec[Stmt[exts]]],
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[FunDecl[exts]]:
    firstToken(self: FunDecl[exts], tokens: Array[Token]) TokenIdx:
        if self.prim_ is Option.Some(t):
            return t

        if self.parentTy is Option.Some(tyId):
            return tyId.firstToken(tokens)

        self.name.token

    lastToken(self: FunDecl[exts], tokens: Array[Token]) TokenIdx:
        match self.body:
            Option.Some(stmts): stmts.last().unwrap().lastToken(tokens)
            Option.None: self.sig.lastToken(tokens)


#[derive(ToDoc)]
type FunSig[exts](
    context: Option[Context[exts]],
    self_: SelfParam[exts],
    params: Vec[FunArg[exts]],
    returnTy: Option[Type[exts]],
    exceptions: Option[Type[exts]],

    ## The '(' token of the argument list. We need to store at least one token
    ## in this node as the minimal node (without context, with empty argument
    ## list, and without return or exception types) won't have any other AST
    ## nodes.
    lparen: TokenIdx,
    ..AstExts[exts].FunSigExts
)


impl[Tokens[AstTyId[exts]]] Tokens[FunSig[exts]]:
    firstToken(self: FunSig[exts], tokens: Array[Token]) TokenIdx:
        if self.context is Option.Some(context):
            return context.firstToken(tokens)

        self.lparen

    lastToken(self: FunSig[exts], tokens: Array[Token]) TokenIdx:
        if self.exceptions is Option.Some(exceptions):
            return exceptions.lastToken(tokens)

        if self.returnTy is Option.Some(returnTy):
            return returnTy.lastToken(tokens)

        let token = self.params.last().map(
            \(lastParam): lastParam.lastToken(tokens),
        ).unwrapOr(self.lparen)

        let rparen = nextNonTrivia(token, tokens).unwrap()
        assert(tokens.get(rparen.idx).kind is TokenKind.RParen)

        rparen


#[derive(ToDoc)]
type FunArg[exts](
    name: Id,
    ty: Option[Type[exts]],
)


impl[Tokens[AstTyId[exts]]] Tokens[FunArg[exts]]:
    firstToken(self: FunArg[exts], tokens: Array[Token]) TokenIdx:
        self.name.token

    lastToken(self: FunArg[exts], tokens: Array[Token]) TokenIdx:
        self.ty.map(\(ty): ty.lastToken(tokens)).unwrapOr(self.name.token)


#[derive(ToDoc)]
type SelfParam[exts]:
    No
    Implicit
    Explicit(Type[exts])


#[derive(ToDoc)]
type ImportDecl(
    ## Import paths, e.g. `[Fir/Prelude, Compiler/Parser]`.
    paths: Vec[Vec[Id]],
)


#[derive(ToDoc)]
type TraitDecl[exts](
    ## Trait name.
    name: Id,

    ## Type parameters of the trait.
    typeParams: Vec[DeclTypeParam[exts]],

    ## Method and associated types of the trait.
    items: Vec[TraitDeclItem[exts]],
    ..AstExts[exts].TraitDeclExts
)


#[derive(ToDoc)]
type TraitDeclItem[exts]:
    ## An associated type declaration, with optional kind.
    Type(
        name: Id,
        kind: Option[Type[exts]],
        default: Option[Type[exts]],
    )
    Fun(FunDecl[exts])


## An `impl` block, implementing a trait for a type.
##
## ```
## impl[ToStr[a]] ToStr[Vec[a]]:
##   toStr(self) Str: ...
##
## impl Iterator[VecIter[a]]:
##   type Item = a
##   next(self) Option[a]: ...
## ```
#[derive(ToDoc)]
type ImplDecl[exts](
    ## Predicates of the `impl` block.
    ##
    ## In the example: `[ToStr[a]]`.
    context: Option[Context[exts]],

    ## The trait name.
    ##
    ## In the example: `ToStr`.
    trait_: AstTyId[exts],

    ## Type[exts] parameters of the trait.
    ##
    ## In the example: `[Vec[a]]`.
    tys: Vec[Type[exts]],

    ## Method and associated type implementations.
    items: Vec[ImplDeclItem[exts]],

    # The `impl` token.
    _firstToken: TokenIdx,
    ..AstExts[exts].ImplDeclExts
)


#[derive(ToDoc)]
type ImplDeclItem[exts]:
    Type(
        assocTy: Id,
        rhs: Type[exts],
    )
    Fun(FunDecl[exts])


#[derive(ToDoc)]
type Type[exts]:
    ## A type constructor, potentially applied some number of arguments. E.g.
    ## `I32`, `Vec[a]`.
    Named(NamedType[exts])

    ## A type variable.
    ##
    ## We don't have higher-kinded types for now, so type variables cannot be
    ## applied.
    Var(Id)

    ## An anonymous record type, e.g. `(x: I32, y: I32)`, `(a: Str, ..r)`.
    Record(RecordType[exts])

    ## An anonymous variant type, e.g. `[Str, Option[U32], ..r]`.
    Variant(VariantType[exts])

    ## A function type: `Fn(I32) Bool / exn`.
    Fn_(FnType[exts])

    ## Associated type selection: `Iterator[iter, exn].Item`.
    AssocTySelect(AssocTySelectType[exts])


impl[Tokens[AstTyId[exts]]] Tokens[Type[exts]]:
    firstToken(self: Type[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Type.Named(ty): ty.firstToken(tokens)
            Type.Var(id): id.token
            Type.Record(ty): ty.firstToken(tokens)
            Type.Variant(ty): ty.firstToken(tokens)
            Type.Fn_(ty): ty.firstToken(tokens)
            Type.AssocTySelect(ty): ty.firstToken(tokens)

    lastToken(self: Type[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Type.Named(ty): ty.lastToken(tokens)
            Type.Var(id): id.token
            Type.Record(ty): ty.lastToken(tokens)
            Type.Variant(ty): ty.lastToken(tokens)
            Type.Fn_(ty): ty.lastToken(tokens)
            Type.AssocTySelect(ty): ty.lastToken(tokens)


#[derive(ToDoc)]
type RecordType[exts](
    fields: Vec[Named[Type[exts]]],
    extension: Option[Type[exts]],
    isRow: Bool,

    # Left paren.
    _firstToken: TokenIdx,

    # Right paren.
    _lastToken: TokenIdx,
)


impl Tokens[RecordType[exts]]:
    firstToken(self: RecordType[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: RecordType[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type VariantType[exts](
    alts: Vec[NamedType[exts]],
    extension: Option[Type[exts]],
    isRow: Bool,

    # Left bracket.
    _firstToken: TokenIdx,

    # Right bracket.
    _lastToken: TokenIdx,
)


impl Tokens[VariantType[exts]]:
    firstToken(self: VariantType[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: VariantType[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type FnType[exts](
    args: Vec[Type[exts]],

    ## Optional return type of the function.
    ret: Option[Type[exts]],

    ## Same as `FunSig.exceptions`.
    exceptions: Option[Type[exts]],

    # The 'Fn' token.
    _firstToken: TokenIdx,

    # The ')' token terminating the argument list. Used as last token when `ret` and `exceptions`
    # are both not available.
    _rparen: TokenIdx,
)


impl[Tokens[AstTyId[exts]]] Tokens[FnType[exts]]:
    firstToken(self: FnType[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: FnType[exts], tokens: Array[Token]) TokenIdx:
        if self.exceptions is Option.Some(ty):
            return ty.lastToken(tokens)

        if self.ret is Option.Some(ty):
            return ty.lastToken(tokens)

        self._rparen


#[derive(ToDoc)]
type AssocTySelectType[exts](
    ty: Type[exts],
    assocTy: Id,
)


impl[Tokens[AstTyId[exts]]] Tokens[AssocTySelectType[exts]]:
    firstToken(self: AssocTySelectType[exts], tokens: Array[Token]) TokenIdx:
        self.ty.firstToken(tokens)

    lastToken(self: AssocTySelectType[exts], tokens: Array[Token]) TokenIdx:
        self.assocTy.token


## Type parameter and predicates of an `impl` or function.
##
## E.g. `[Iterator[iter, exn], Debug[item]]`.
#[derive(ToDoc)]
type Context[exts](
    ## Predicates: `Iterator[iter, exn]` and `Debug[item]` in the example.
    preds: Vec[Pred_[exts]],

    # Left bracket.
    _firstToken: TokenIdx,

    # Right bracket.
    _lastToken: TokenIdx,
)


## A predicate in a context. E.g. in context
##
##     [Iterator[iter, exn],
##      Iterator[iter, exn].Item = item,
##      Debug[item]]
##
## We have three predicates:
##
## - `Iterator[iter, exn]`              (`Pred.App`)
## - `Iterator[iter, exn].Item = item`  (`Pred.AssocTyEq`)
## - `Debug[item]`                      (`Pred.App`)
##
#[derive(ToDoc)]
type Pred_[exts]:
    ## A kind annotation: `ext: Row[Rec]`.
    Kind(
        name: Id,
        kind: Option[Type[exts]],
    )

    ## A trait application: `Iterator[iter, exn]`.
    App(NamedType[exts])

    ## An associated type equality: `Iterator[iter, exn].Item = U32`.
    AssocTyEq(
        ty: NamedType[exts],
        assocTy: Id,
        eq: Type[exts],
    )


impl[Tokens[AstTyId[exts]]] Tokens[Pred_[exts]]:
    firstToken(self: Pred_[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Pred_.Kind(name = kindVar, ..): kindVar.firstToken(tokens)
            Pred_.App(app): app.firstToken(tokens)
            Pred_.AssocTyEq(ty, ..): ty.firstToken(tokens)

    lastToken(self: Pred_[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Pred_.Kind(name = _, kind):
                match kind:
                    Option.Some(kind): kind.lastToken(tokens)
                    Option.None: self.firstToken(tokens)
            Pred_.App(app): app.lastToken(tokens)
            Pred_.AssocTyEq(eq, ..): eq.lastToken(tokens)


## A type parameter in a type or trait declaration, with optional kind annotation.
##
## E.g. `t` in `type Vec[t]`, `r: Row[Rec]` in `trait Foo[r: Row[Rec]]`.
#[derive(ToDoc)]
type DeclTypeParam[exts](
    ## Name of the type parameter.
    name: Id,

    ## Optional kind annotation.
    kind: Option[Type[exts]],
)


impl[Tokens[AstTyId[exts]]] Tokens[DeclTypeParam[exts]]:
    firstToken(self: DeclTypeParam[exts], tokens: Array[Token]) TokenIdx:
        self.name.token

    lastToken(self: DeclTypeParam[exts], tokens: Array[Token]) TokenIdx:
        match self.kind:
            Option.Some(kind): kind.lastToken(tokens)
            Option.None: self.name.token


impl Tokens[Context[exts]]:
    firstToken(self: Context[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: Context[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


## A named type, e.g. `I32`, `Vec[I32]`, `Iterator[iter, exn]`.
#[derive(ToDoc)]
type NamedType[exts](
    ## Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    name: AstTyId[exts],

    ## Arguments of the type constructor.
    args: Option[TyArgs[exts]],
)


NamedType.numTyArgs(self: NamedType[exts]) U32:
    match self.args:
        Option.None: 0
        Option.Some(args): args.args.len()


impl[Tokens[AstTyId[exts]]] Tokens[NamedType[exts]]:
    firstToken(self: NamedType[exts], tokens: Array[Token]) TokenIdx:
        self.name.firstToken(tokens)

    lastToken(self: NamedType[exts], tokens: Array[Token]) TokenIdx:
        match self.args:
            Option.Some(args): args.lastToken(tokens)
            Option.None: self.name.lastToken(tokens)


#[derive(ToDoc)]
type Named[t](
    name: Option[Id],
    node: t,
)


impl[Tokens[t]] Tokens[Named[t]]:
    firstToken(self: Named[t], tokens: Array[Token]) TokenIdx:
        match self.name:
            Option.Some(name): name.token
            Option.None: self.node.firstToken(tokens)

    lastToken(self: Named[t], tokens: Array[Token]) TokenIdx:
        self.node.lastToken(tokens)


#[derive(ToDoc)]
type Stmt[exts]:
    Let(LetStmt[exts])
    Assign(AssignStmt[exts])
    Expr(Expr[exts])
    For(ForStmt[exts])
    While(WhileStmt[exts])
    Loop(LoopStmt[exts])
    Break(BreakStmt)
    Continue(ContinueStmt)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[Stmt[exts]]:
    firstToken(self: Stmt[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Stmt.Let(e): e.firstToken(tokens)
            Stmt.Assign(e): e.firstToken(tokens)
            Stmt.Expr(e): e.firstToken(tokens)
            Stmt.For(e): e.firstToken(tokens)
            Stmt.While(e): e.firstToken(tokens)
            Stmt.Loop(e): e.firstToken(tokens)
            Stmt.Break(e): e.firstToken(tokens)
            Stmt.Continue(e): e.firstToken(tokens)

    lastToken(self: Stmt[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Stmt.Let(e): e.lastToken(tokens)
            Stmt.Assign(e): e.lastToken(tokens)
            Stmt.Expr(e): e.lastToken(tokens)
            Stmt.For(e): e.lastToken(tokens)
            Stmt.While(e): e.lastToken(tokens)
            Stmt.Loop(e): e.lastToken(tokens)
            Stmt.Break(e): e.lastToken(tokens)
            Stmt.Continue(e): e.lastToken(tokens)


## A let statement: `let x: T = expr`.
#[derive(ToDoc)]
type LetStmt[exts](
    lhs: Pat[exts],
    ty: Option[Type[exts]],
    rhs: Expr[exts],
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[LetStmt[exts]]:
    firstToken(self: LetStmt[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: LetStmt[exts], tokens: Array[Token]) TokenIdx:
        self.rhs.lastToken(tokens)


#[derive(ToDoc)]
type AssignStmt[exts](
    lhs: Expr[exts],
    rhs: Expr[exts],
    op: AssignOp,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[AssignStmt[exts]]:
    firstToken(self: AssignStmt[exts], tokens: Array[Token]) TokenIdx:
        self.lhs.firstToken(tokens)

    lastToken(self: AssignStmt[exts], tokens: Array[Token]) TokenIdx:
        self.rhs.lastToken(tokens)


#[derive(ToDoc)]
type AssignOp:
    Eq
    PlusEq
    MinusEq
    StarEq
    CaretEq


#[derive(ToDoc)]
type ForStmt[exts](
    label: Option[Id],
    pat: Pat[exts],

    ## Type annotation on the loop variable, the `Item` associated type in `Iterator[iter, exn]`.
    astTy: Option[Type[exts]],

    expr: Expr[exts],

    body: Vec[Stmt[exts]],

    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[ForStmt[exts]]:
    firstToken(self: ForStmt[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: ForStmt[exts], tokens: Array[Token]) TokenIdx:
        self.body.last().unwrap().lastToken(tokens)


#[derive(ToDoc)]
type WhileStmt[exts](
    label: Option[Id],
    cond: Expr[exts],
    body: Vec[Stmt[exts]],
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[WhileStmt[exts]]:
    firstToken(self: WhileStmt[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: WhileStmt[exts], tokens: Array[Token]) TokenIdx:
        self.body.last().unwrap().lastToken(tokens)


#[derive(ToDoc)]
type LoopStmt[exts](
    body: Vec[Stmt[exts]],
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[LoopStmt[exts]]:
    firstToken(self: LoopStmt[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: LoopStmt[exts], tokens: Array[Token]) TokenIdx:
        self.body.last().unwrap().lastToken(tokens)


#[derive(ToDoc)]
type BreakStmt(
    label: Option[Id],

    ## How many levels of loops to break. Parser initializes this as 0, type checker updates
    ## based on the labels of enclosing loops.
    level: U32,

    _firstToken: TokenIdx,
)


impl Tokens[BreakStmt]:
    firstToken(self: BreakStmt, tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: BreakStmt, tokens: Array[Token]) TokenIdx:
        match self.label:
            Option.Some(id): id.lastToken(tokens)
            Option.None: self._firstToken


#[derive(ToDoc)]
type ContinueStmt(
    label: Option[Id],

    ## Same as `BreakStmt.level`.
    level: U32,

    _firstToken: TokenIdx,
)


impl Tokens[ContinueStmt]:
    firstToken(self: ContinueStmt, tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: ContinueStmt, tokens: Array[Token]) TokenIdx:
        match self.label:
            Option.Some(id): id.lastToken(tokens)
            Option.None: self._firstToken


#[derive(ToDoc)]
type Pat[exts]:
    ## Matches anything, binds it to variable.
    Var(VarPat)

    ## Matches a constructor.
    Con(ConPat[exts])

    ## Underscore, aka. wildcard.
    Ignore(TokenIdx)

    ## Matches the string.
    Str(Str, TokenIdx)

    ## Matches the character.
    Char(Char, TokenIdx)

    ## Or pattern: `<pat1> | <pat2> | ...`. At least two patterns.
    Or(Vec[Pat[exts]])

    Record(RecordPat[exts])

    ## Variant pattern: `~"hi"`, `~Option.Some(_)`.
    Variant(VariantPat[exts])


impl[Tokens[AstTyId[exts]]] Tokens[Pat[exts]]:
    firstToken(self: Pat[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Pat.Var(pat): pat.firstToken(tokens)

            Pat.Con(pat): pat.firstToken(tokens)

            Pat.Record(pat): pat.firstToken(tokens)

            Pat.Ignore(tok) | Pat.Str(_, tok) | Pat.Char(_, tok): tok

            Pat.Or(ps): ps.get(0).firstToken(tokens)

            Pat.Variant(pat): pat.firstToken(tokens)

    lastToken(self: Pat[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Pat.Var(pat): pat.lastToken(tokens)

            Pat.Con(pat): pat.lastToken(tokens)

            Pat.Record(pat): pat.lastToken(tokens)

            Pat.Ignore(tok) | Pat.Char(_, tok): tok

            # A string pattern is always a `BEGIN_STR` and `END_STR`,
            # interpolation not allowed.
            Pat.Str(_, tok): TokenIdx(idx = tok.idx + 1)

            Pat.Or(ps): ps.last().unwrap().lastToken(tokens)

            Pat.Variant(pat): pat.lastToken(tokens)


#[derive(ToDoc)]
type VarPat(
    var_: Id,
)


impl Tokens[VarPat]:
    firstToken(self: VarPat, tokens: Array[Token]) TokenIdx:
        self.var_.firstToken(tokens)

    lastToken(self: VarPat, tokens: Array[Token]) TokenIdx:
        self.var_.lastToken(tokens)


#[derive(ToDoc)]
type RestPat:
    No
    Ignore
    Bind(VarPat)


#[derive(ToDoc)]
type ConPat[exts](
    con: Con[exts],
    fields: Vec[Named[Pat[exts]]],
    rest: RestPat,
    _lastToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]]] Tokens[ConPat[exts]]:
    firstToken(self: ConPat[exts], tokens: Array[Token]) TokenIdx:
        self.con.firstToken(tokens)

    lastToken(self: ConPat[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type RecordPat[exts](
    fields: Vec[Named[Pat[exts]]],
    rest: RestPat,
    _firstToken: TokenIdx,
    _lastToken: TokenIdx,
    ..AstExts[exts].RecordPatExts
)


impl Tokens[RecordPat[exts]]:
    firstToken(self: RecordPat[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: RecordPat[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type VariantPat[exts](
    pat: Pat[exts],
    ..AstExts[exts].VariantPatExts
)


impl[Tokens[AstTyId[exts]]] Tokens[VariantPat[exts]]:
    firstToken(self: VariantPat[exts], tokens: Array[Token]) TokenIdx:
        let tilde = prevNonTrivia(self.pat.firstToken(tokens), tokens).unwrap()
        assert(tokens.get(tilde.idx).kind is TokenKind.Tilde)
        tilde

    lastToken(self: VariantPat[exts], tokens: Array[Token]) TokenIdx:
        self.pat.lastToken(tokens)


## A sum or product constructor, in patterns and expressions.
#[derive(ToDoc)]
type Con[exts](
    ## Type of the constructor.
    ty: AstTyId[exts],

    ## Name of the constructor. Only in sum types.
    con: Option[Id],

    ## Type arguments explicitly passed to the variable.
    ##
    ## Always `Option.None` in patterns.
    userTyArgs: Option[TyArgs[exts]],

    # In variant constructors we'll see a '~' before `ty`, so we can't use `ty` as the first token.
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]]] Tokens[Con[exts]]:
    firstToken(self: Con[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: Con[exts], tokens: Array[Token]) TokenIdx:
        match self.userTyArgs:
            Option.Some(tyArgs): tyArgs.lastToken(tokens)
            Option.None:
                match self.con:
                    Option.Some(con): con.token
                    Option.None: self.ty.lastToken(tokens)


#[derive(ToDoc)]
type Expr[exts]:
    ## A variable: `x`.
    Var(VarExpr[exts])

    ## A constructor: `Option.None`, `Result.Ok`, `Bool.True`, `Vec`.
    ConSel(Con[exts])

    ## A field selection: `<expr>.x` where `x` is a field.
    ##
    ## Parser generates this node for all expression of form `<expr>.<id>`, type checker converts
    ## method selection expressions to `MethodSel`.
    FieldSel(FieldSelExpr[exts])

    ## An associated function or method selection:
    ##
    ## - Associated function: `Vec.withCapacity`.
    ## - Method: `Vec.push`.
    AssocFnSel(AssocFnSelExpr[exts])

    ## A function call: `f(a)`.
    Call(CallExpr[exts])

    ## An integer literal.
    Int(IntExpr)

    ## A string literal.
    Str(StrExpr[exts])

    ## A character literal.
    Char(CharExpr)

    ## A binary operator: `x + y`, `i >> 2`.
    ##
    ## Some of the binary operators are desugared to method calls by the type checker.
    BinOp(BinOpExpr[exts])

    ## A unary operator: `-x`, `not b`.
    ##
    ## Some of the unary operators are desugared to method calls by the type checker.
    UnOp(UnOpExpr[exts])

    Return(ReturnExpr[exts])

    Match(MatchExpr[exts])

    If(IfExpr[exts])

    Fn_(FnExpr[exts])

    Is(IsExpr[exts])

    Do(DoExpr[exts])

    ## A sequence: `[a, b, c]`, `[a = b, c = d]`, `Vec.[...]`. Can be empty.
    Seq(SeqExpr[exts])

    ## A parenthesized expression.
    Paren(ParenExpr[exts])

    ## A record: `(1, 2)`, `(x = 123, msg = "hi")`.
    Record(RecordExpr[exts])

    ## A variant: `~"hi"`, `Option.Some(123)`.
    Variant(VariantExpr[exts])


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[Expr[exts]]:
    firstToken(self: Expr[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Expr.Var(e): e.firstToken(tokens)
            Expr.ConSel(e): e.firstToken(tokens)
            Expr.FieldSel(e): e.firstToken(tokens)
            Expr.AssocFnSel(e): e.firstToken(tokens)
            Expr.Call(e): e.firstToken(tokens)
            Expr.Int(e): e.firstToken(tokens)
            Expr.Str(e): e.firstToken(tokens)
            Expr.Char(e): e.firstToken(tokens)
            Expr.BinOp(e): e.firstToken(tokens)
            Expr.UnOp(e): e.firstToken(tokens)
            Expr.Record(e): e.firstToken(tokens)
            Expr.Return(e): e.firstToken(tokens)
            Expr.Match(e): e.firstToken(tokens)
            Expr.If(e): e.firstToken(tokens)
            Expr.Fn_(e): e.firstToken(tokens)
            Expr.Is(e): e.firstToken(tokens)
            Expr.Do(e): e.firstToken(tokens)
            Expr.Seq(e): e.firstToken(tokens)
            Expr.Paren(e): e.firstToken(tokens)
            Expr.Variant(e): e.firstToken(tokens)

    lastToken(self: Expr[exts], tokens: Array[Token]) TokenIdx:
        match self:
            Expr.Var(e): e.lastToken(tokens)
            Expr.ConSel(e): e.lastToken(tokens)
            Expr.FieldSel(e): e.lastToken(tokens)
            Expr.AssocFnSel(e): e.lastToken(tokens)
            Expr.Call(e): e.lastToken(tokens)
            Expr.Int(e): e.lastToken(tokens)
            Expr.Str(e): e.lastToken(tokens)
            Expr.Char(e): e.lastToken(tokens)
            Expr.BinOp(e): e.lastToken(tokens)
            Expr.UnOp(e): e.lastToken(tokens)
            Expr.Record(e): e.lastToken(tokens)
            Expr.Return(e): e.lastToken(tokens)
            Expr.Match(e): e.lastToken(tokens)
            Expr.If(e): e.lastToken(tokens)
            Expr.Fn_(e): e.lastToken(tokens)
            Expr.Is(e): e.lastToken(tokens)
            Expr.Do(e): e.lastToken(tokens)
            Expr.Seq(e): e.lastToken(tokens)
            Expr.Paren(e): e.lastToken(tokens)
            Expr.Variant(e): e.lastToken(tokens)


#[derive(ToDoc)]
type VarExpr[exts](
    id: AstVarId[exts],

    ## Type arguments explicitly passed to the variable.
    userTyArgs: Option[TyArgs[exts]],
)


impl[Tokens[AstVarId[exts]]] Tokens[VarExpr[exts]]:
    firstToken(self: VarExpr[exts], tokens: Array[Token]) TokenIdx:
        self.id.firstToken(tokens)

    lastToken(self: VarExpr[exts], tokens: Array[Token]) TokenIdx:
        match self.userTyArgs:
            Option.Some(tyArgs): tyArgs.lastToken(tokens)
            Option.None: self.id.lastToken(tokens)


#[derive(ToDoc)]
type TyArgs[exts](
    args: Vec[Type[exts]],

    # Left bracket.
    _firstToken: TokenIdx,

    # Right bracket.
    _lastToken: TokenIdx,
)


impl Tokens[TyArgs[exts]]:
    firstToken(self: TyArgs[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: TyArgs[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type FieldSelExpr[exts](
    object: Expr[exts],

    field: Id,

    ## Type arguments explicitly passed to the variable.
    ##
    ## Since fields can't have `forall` quantifiers, this will only be valid when the field is a
    ## method, in which case the type checker will convert this node into `MethodSelExpr[exts]`.
    userTyArgs: Option[TyArgs[exts]],
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[FieldSelExpr[exts]]:
    firstToken(self: FieldSelExpr[exts], tokens: Array[Token]) TokenIdx:
        self.object.firstToken(tokens)

    lastToken(self: FieldSelExpr[exts], tokens: Array[Token]) TokenIdx:
        match self.userTyArgs:
            Option.Some(tyArgs): tyArgs.lastToken(tokens)
            Option.None: self.field.lastToken(tokens)


## An associated function or method selection:
##
## - Associated function: `Vec.withCapacity`.
## - Method: `Vec.push`.
#[derive(ToDoc)]
type AssocFnSelExpr[exts](
    # The type of the associated function: `Vec` in the examples above.
    ty: AstTyId[exts],

    # The associated function name: `withCapacity` and `push` in the examples
    # above.
    member: AstAssocVarId[exts],

    ## Type arguments explicitly passed to the variable.
    userTyArgs: Option[TyArgs[exts]],

    _lastToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[AssocFnSelExpr[exts]]:
    firstToken(self: AssocFnSelExpr[exts], tokens: Array[Token]) TokenIdx:
        self.ty.firstToken(tokens)

    lastToken(self: AssocFnSelExpr[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type CallExpr[exts](
    fun: Expr[exts],
    args: Vec[Named[Expr[exts]]],
    splice: Option[Expr[exts]],
    _lastToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[CallExpr[exts]]:
    firstToken(self: CallExpr[exts], tokens: Array[Token]) TokenIdx:
        self.fun.firstToken(tokens)

    lastToken(self: CallExpr[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type IntExpr(
    ## The digits of the integer, without any prefix ("0x" or "0b") and suffix ("u32" etc.).
    ##
    ## The digits will be parsed during type checking. If the integer doesn't have a suffix, parsing
    ## will be done based on the inferred type of the integer.
    text: Str,

    ## The type checker updates this based on the inferred type of the integer.
    suffix: Option[IntKind],

    radix: U32,

    ## Filled in by the type checker. The parsed integer.
    ##
    ## This will be the integer value in two's complement, extended to unsiged 32-bit.
    ## E.g. `-1u8` will be `0x000000ff`, instead of `0xffffffff`.
    parsed: U32,

    token: TokenIdx,
)


impl Tokens[IntExpr]:
    firstToken(self: IntExpr, tokens: Array[Token]) TokenIdx:
        self.token

    lastToken(self: IntExpr, tokens: Array[Token]) TokenIdx:
        self.token


#[derive(ToDoc)]
type StrExpr[exts](
    parts: Vec[StrPart[exts]],
    first: TokenIdx,
    last: TokenIdx,
)


impl Tokens[StrExpr[exts]]:
    firstToken(self: StrExpr[exts], tokens: Array[Token]) TokenIdx:
        self.first

    lastToken(self: StrExpr[exts], tokens: Array[Token]) TokenIdx:
        self.last


#[derive(ToDoc)]
type StrPart[exts]:
    Str(Str)
    Expr(Expr[exts])


#[derive(ToDoc)]
type CharExpr(
    char: Char,
    token: TokenIdx,
)


impl Tokens[CharExpr]:
    firstToken(self: CharExpr, tokens: Array[Token]) TokenIdx:
        self.token

    lastToken(self: CharExpr, tokens: Array[Token]) TokenIdx:
        self.token


#[derive(ToDoc)]
type BinOpExpr[exts](
    left: Expr[exts],
    right: Expr[exts],
    op: BinOp,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[BinOpExpr[exts]]:
    firstToken(self: BinOpExpr[exts], tokens: Array[Token]) TokenIdx:
        self.left.firstToken(tokens)

    lastToken(self: BinOpExpr[exts], tokens: Array[Token]) TokenIdx:
        self.right.lastToken(tokens)


#[derive(ToDoc, Eq)]
type BinOp:
    Add
    And
    BitAnd
    BitOr
    Divide
    Equal
    Gt
    GtEq
    LeftShift
    Lt
    LtEq
    Multiply
    NotEqual
    Or
    RightShift
    Subtract


#[derive(ToDoc)]
type UnOpExpr[exts](
    op: UnOp,
    expr: Expr[exts],
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[UnOpExpr[exts]]:
    firstToken(self: UnOpExpr[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: UnOpExpr[exts], tokens: Array[Token]) TokenIdx:
        self.expr.lastToken(tokens)


#[derive(ToDoc)]
type RecordExpr[exts](
    fields: Vec[Named[Expr[exts]]],
    splice: Option[Expr[exts]],
    _firstToken: TokenIdx,
    _lastToken: TokenIdx,
)


impl Tokens[RecordExpr[exts]]:
    firstToken(self: RecordExpr[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: RecordExpr[exts], tokens: Array[Token]) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type VariantExpr[exts](
    expr: Expr[exts],
    ..AstExts[exts].InferredTyExts
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[VariantExpr[exts]]:
    firstToken(self: VariantExpr[exts], tokens: Array[Token]) TokenIdx:
        let tilde = prevNonTrivia(self.expr.firstToken(tokens), tokens).unwrap()
        assert(tokens.get(tilde.idx).kind is TokenKind.Tilde)
        tilde

    lastToken(self: VariantExpr[exts], tokens: Array[Token]) TokenIdx:
        self.expr.lastToken(tokens)


#[derive(ToDoc)]
type ReturnExpr[exts](
    expr: Option[Expr[exts]],
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[ReturnExpr[exts]]:
    firstToken(self: ReturnExpr[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: ReturnExpr[exts], tokens: Array[Token]) TokenIdx:
        match self.expr:
            Option.Some(expr): expr.lastToken(tokens)
            Option.None: self._firstToken


#[derive(ToDoc)]
type MatchExpr[exts](
    scrutinee: Expr[exts],
    alts: Vec[Alt[exts]],
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[MatchExpr[exts]]:
    firstToken(self: MatchExpr[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: MatchExpr[exts], tokens: Array[Token]) TokenIdx:
        self.alts.last().unwrap().lastToken(tokens)


#[derive(ToDoc)]
type Alt[exts](
    pat: Pat[exts],
    guard: Option[Expr[exts]],
    rhs: Vec[Stmt[exts]],
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[Alt[exts]]:
    firstToken(self: Alt[exts], tokens: Array[Token]) TokenIdx:
        self.pat.firstToken(tokens)

    lastToken(self: Alt[exts], tokens: Array[Token]) TokenIdx:
        self.rhs.last().unwrap().lastToken(tokens)


#[derive(ToDoc)]
type IfExpr[exts](
    # At least one element
    branches: Vec[IfBranch[exts]],
    elseBranch: Option[Vec[Stmt[exts]]],
    _firstToken: TokenIdx,
)


#[derive(ToDoc)]
type IfBranch[exts](
    guard: Expr[exts],
    body: Vec[Stmt[exts]],
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[IfExpr[exts]]:
    firstToken(self: IfExpr[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: IfExpr[exts], tokens: Array[Token]) TokenIdx:
        if self.elseBranch is Option.Some(block):
            return block.last().unwrap().lastToken(tokens)

        self.branches.last().unwrap().body.last().unwrap().lastToken(tokens)


#[derive(ToDoc)]
type FnExpr[exts](
    sig: FunSig[exts],
    body: Vec[Stmt[exts]],
    idx: U32,
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[FnExpr[exts]]:
    firstToken(self: FnExpr[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: FnExpr[exts], tokens: Array[Token]) TokenIdx:
        self.body.last().unwrap().lastToken(tokens)


# <expr> is <pat>
#[derive(ToDoc)]
type IsExpr[exts](
    expr: Expr[exts],
    pat: Pat[exts],
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[IsExpr[exts]]:
    firstToken(self: IsExpr[exts], tokens: Array[Token]) TokenIdx:
        self.expr.firstToken(tokens)

    lastToken(self: IsExpr[exts], tokens: Array[Token]) TokenIdx:
        self.pat.lastToken(tokens)


#[derive(ToDoc)]
type DoExpr[exts](
    body: Vec[Stmt[exts]],
    _firstToken: TokenIdx,
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[DoExpr[exts]]:
    firstToken(self: DoExpr[exts], tokens: Array[Token]) TokenIdx:
        self._firstToken

    lastToken(self: DoExpr[exts], tokens: Array[Token]) TokenIdx:
        self.body.last().unwrap().lastToken(tokens)


#[derive(ToDoc)]
type UnOp:
    Not
    Neg


#[derive(ToDoc)]
type SeqExpr[exts](
    ty: Option[Type[exts]],
    elems: Vec[SeqElem[exts]],
    _lbracket: TokenIdx,
    _rbracket: TokenIdx,
)


#[derive(ToDoc)]
type SeqElem[exts](
    key: Option[Expr[exts]],
    val: Expr[exts],
)


impl[Tokens[AstTyId[exts]], Tokens[AstVarId[exts]]] Tokens[SeqExpr[exts]]:
    firstToken(self: SeqExpr[exts], tokens: Array[Token]) TokenIdx:
        match self.ty:
            Option.Some(ty): ty.firstToken(tokens)
            Option.None: self._lbracket

    lastToken(self: SeqExpr[exts], tokens: Array[Token]) TokenIdx:
        self._rbracket


#[derive(ToDoc)]
type ParenExpr[exts](
    expr: Expr[exts],
    _lparen: TokenIdx,
    _rparen: TokenIdx,
)


impl Tokens[ParenExpr[exts]]:
    firstToken(self: ParenExpr[exts], tokens: Array[Token]) TokenIdx:
        self._lparen

    lastToken(self: ParenExpr[exts], tokens: Array[Token]) TokenIdx:
        self._rparen


## An attribute: `#[derive(Foo, Bar)]`, `#[F(x = 1, y = "hi")]`.
##
## This just uses expression syntax as expression syntax should be rich enough
## to cover most attributes. We may revise this as needed.
#[derive(ToDoc)]
type Attribute[exts](
    expr: Expr[exts],

    # "#["
    open: TokenIdx,

    # "]"
    close: TokenIdx,
)
