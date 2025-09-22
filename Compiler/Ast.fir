import [
    # imports Loc
    # TODO: Why is Loc in Error module?
    Compiler/Error,
    # imports IntKind
    Compiler/Token,
]


#[derive(ToDoc)]
type TokenIdx(
    idx: U32,
)


impl Step[TokenIdx]:
    step(self: TokenIdx) TokenIdx:
        TokenIdx(idx = self.idx + 1)


impl Ord[TokenIdx]:
    cmp(self: TokenIdx, other: TokenIdx) Ordering:
        self.idx.cmp(other.idx)


trait Tokens[t]:
    firstToken(self: t) TokenIdx

    lastToken(self: t) TokenIdx


#[derive(ToDoc)]
type Id(
    token: TokenIdx,
)


impl Tokens[Id]:
    firstToken(self: Id) TokenIdx:
        self.token

    lastToken(self: Id) TokenIdx:
        self.token


## A top-level declaration.
#[derive(ToDoc)]
type TopDecl:
    ## A type declaration: `type T: ...`.
    Type(TypeDecl)

    ## A function declaration: `f(...) = ...`.
    Fun(FunDecl)

    ## An import declaration.
    Import(ImportDecl)

    ## A trait declaration.
    Trait(TraitDecl)

    ## An `impl` block, implementing a trait or associated methods for a type.
    Impl(ImplDecl)


## A type declaration: `type Vec[t]: ...`.
#[derive(ToDoc)]
type TypeDecl(
    ## When the type is a primitive, the `prim` token.
    prim_: Option[TokenIdx],

    ## The type name. `Vec` in the example.
    name: Id,

    ## Type parameters of the type. `[t]` in the example.
    typeParams: Vec[Id],

    ## Kinds of `type_params`. Filled in by kind inference.
    typeParamKinds: Vec[Kind],

    ## Constructors of the type.
    rhs: Option[TypeDeclRhs],
)


## Constructors of a type declaration.
#[derive(ToDoc)]
type TypeDeclRhs:
    ## A sum type, with more than one constructor.
    Sum(Vec[ConDecl])

    ## A product type uses the type name as the constructor and only has fields.
    Product(ConFields)


## A sum type constructor.
#[derive(ToDoc)]
type ConDecl(
    name: Id,
    fields: ConFields,
    _lastToken: TokenIdx,
)


#[derive(ToDoc)]
type Kind:
    Star
    Row(RecordOrVariant)


#[derive(ToDoc)]
type RecordOrVariant:
    Record
    Variant


#[derive(ToDoc)]
type ConFields:
    Empty
    Named(Vec[NamedField])
    Unnamed(Vec[Type])


#[derive(ToDoc)]
type NamedField(
    name: Id,
    ty: Type,
)


#[derive(ToDoc)]
type FunDecl(
    ## When the function is a primitive, the `prim` token.
    prim_: Option[TokenIdx],

    ## Only in associated functions: the parent type. E.g. `Vec` in `Vec.push(...) = ...`.
    parentTy: Option[Id],

    ## Name of the function.
    name: Id,

    ## Type signature of the function.
    sig: FunSig,

    ## Body (code) of the function. Not available in `prim` functions.
    body: Option[Vec[Stmt]],
)


#[derive(ToDoc)]
type FunSig(
    context: Option[Context],
    self_: SelfParam,
    params: Vec[FunArg],
    exceptions: Option[Type],
    returnTy: Option[Type],
)


#[derive(ToDoc)]
type FunArg(
    name: Id,
    ty: Option[Type],
)


#[derive(ToDoc)]
type SelfParam:
    No
    Implicit
    Explicit(Type)


#[derive(ToDoc)]
type ImportDecl(
    ## Import paths, e.g. `[Fir/Prelude, Compiler/Parser]`.
    paths: Vec[Vec[Id]],
)


#[derive(ToDoc)]
type TraitDecl(
    ## Trait name.
    name: Id,

    ## Type parameters of the trait.
    typeParams: Vec[Id],

    ## Kinds of `type_params`. Filled in by kind inference.
    typeParamKinds: Vec[Kind],

    ## Methods of the trait.
    items: Vec[FunDecl],
)


## An `impl` block, implementing a trait for a type.
##
## ```
## impl[ToStr[a]] ToStr[Vec[a]]:
##   toStr(self): Str = ...
##
## impl Iterator[VecIter[a], a]:
##   next(self): Option[a] = ...
## ```
#[derive(ToDoc)]
type ImplDecl(
    ## Predicates of the `impl` block.
    ##
    ## In the example: `[ToStr[a]]`.
    context: Option[Context],

    ## The trait name.
    ##
    ## In the example: `ToStr`.
    trait_: Id,

    ## Type parameters of the trait.
    ##
    ## In the example: `[Vec[a]]`.
    tys: Vec[Type],

    ## Method implementations.
    items: Vec[FunDecl],

    # The `impl` token.
    _firstToken: TokenIdx,
)


#[derive(ToDoc)]
type Type:
    ## A type constructor, potentially applied some number of arguments. E.g. `I32`, `Vec[T]`.
    Named(NamedType)

    ## A type variable.
    ##
    ## We don't have higher-kinded types for now, so type variables cannot be applied.
    Var(Id)

    ## An anonymous record type, e.g. `(x: I32, y: I32)`, `(a: Str, ..R)`.
    Record(RecordType)

    ## An anonymous variant type, e.g. `[Error(msg: Str), Ok, ..R]`.
    Variant(VariantType)

    ## A function type: `Fn(I32): Bool`.
    Fn_(FnType)


impl Tokens[Type]:
    firstToken(self: Type) TokenIdx:
        match self:
            Type.Named(ty): ty.firstToken()
            Type.Var(id): id.token
            Type.Record(ty): ty.firstToken()
            Type.Variant(ty): ty.firstToken()
            Type.Fn_(ty): ty.firstToken()

    lastToken(self: Type) TokenIdx:
        match self:
            Type.Named(ty): ty.lastToken()
            Type.Var(id): id.token
            Type.Record(ty): ty.lastToken()
            Type.Variant(ty): ty.lastToken()
            Type.Fn_(ty): ty.lastToken()


#[derive(ToDoc)]
type RecordType(
    fields: Vec[Named[Type]],
    extension: Option[Id],
    isRow: Bool,

    # Left paren.
    _firstToken: TokenIdx,

    # Right paren.
    _lastToken: TokenIdx,
)


impl Tokens[RecordType]:
    firstToken(self: RecordType) TokenIdx:
        self._firstToken

    lastToken(self: RecordType) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type VariantType(
    alts: Vec[NamedType],
    extension: Option[Id],
    isRow: Bool,

    # Left bracket.
    _firstToken: TokenIdx,

    # Right bracket.
    _lastToken: TokenIdx,
)


impl Tokens[VariantType]:
    firstToken(self: VariantType) TokenIdx:
        self._firstToken

    lastToken(self: VariantType) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type FnType(
    args: Vec[Type],

    ## Optional return type of the function.
    ret: Option[Type],

    ## Same as `FunSig.exceptions`.
    exceptions: Option[Type],

    # The 'Fn' token.
    _firstToken: TokenIdx,

    # The ')' token terminating the argument list. Used as last token when `ret` and `exceptions`
    # are both not available.
    _rparen: TokenIdx,
)


impl Tokens[FnType]:
    firstToken(self: FnType) TokenIdx:
        self._firstToken

    lastToken(self: FnType) TokenIdx:
        if self.exceptions is Option.Some(ty):
            return ty.lastToken()

        if self.ret is Option.Some(ty):
            return ty.lastToken()

        self._rparen


## Type parameter and predicates of an `impl` or function.
##
## E.g. `[Iterator[iter, item], Debug[item]]`.
#[derive(ToDoc)]
type Context(
    ## Type parameters, generated by the type checker.
    typeParams: Vec[TypeParam],

    ## Predicates: `Iterator[iter, item]` and `Debug[item]` in the example.
    preds: Vec[Type],

    # Left bracket.
    _firstToken: TokenIdx,

    # Right bracket.
    _lastToken: TokenIdx,
)


#[derive(ToDoc)]
type TypeParam(
    name: Id,
    kind: Kind,
)


impl Tokens[Context]:
    firstToken(self: Context) TokenIdx:
        self._firstToken

    lastToken(self: Context) TokenIdx:
        self._lastToken


## A named type, e.g. `I32`, `Vec[I32]`, `Iterator[coll, Str]`.
#[derive(ToDoc)]
type NamedType(
    ## Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    name: Id,

    ## Arguments of the type constructor.
    args: Option[TyArgs],
)


impl Tokens[NamedType]:
    firstToken(self: NamedType) TokenIdx:
        self.name.token

    lastToken(self: NamedType) TokenIdx:
        match self.args:
            Option.Some(args): args.lastToken()
            Option.None: self.name.token


#[derive(ToDoc)]
type Named[t](
    name: Option[Id],
    node: t,
)


impl[Tokens[t]] Tokens[Named[t]]:
    firstToken(self: Named[t]) TokenIdx:
        match self.name:
            Option.Some(name): name.token
            Option.None: self.node.firstToken()

    lastToken(self: Named[t]) TokenIdx:
        self.node.lastToken()


#[derive(ToDoc)]
type Stmt:
    Let(LetStmt)
    Assign(AssignStmt)
    Expr(Expr)
    For(ForStmt)
    While(WhileStmt)
    Loop(LoopStmt)
    Break(BreakStmt)
    Continue(ContinueStmt)


impl Tokens[Stmt]:
    firstToken(self: Stmt) TokenIdx:
        match self:
            Stmt.Let(e): e.firstToken()
            Stmt.Assign(e): e.firstToken()
            Stmt.Expr(e): e.firstToken()
            Stmt.For(e): e.firstToken()
            Stmt.While(e): e.firstToken()
            Stmt.Loop(e): e.firstToken()
            Stmt.Break(e): e.firstToken()
            Stmt.Continue(e): e.firstToken()

    lastToken(self: Stmt) TokenIdx:
        match self:
            Stmt.Let(e): e.lastToken()
            Stmt.Assign(e): e.lastToken()
            Stmt.Expr(e): e.lastToken()
            Stmt.For(e): e.lastToken()
            Stmt.While(e): e.lastToken()
            Stmt.Loop(e): e.lastToken()
            Stmt.Break(e): e.lastToken()
            Stmt.Continue(e): e.lastToken()


## A let statement: `let x: T = expr`.
#[derive(ToDoc)]
type LetStmt(
    lhs: Pat,
    ty: Option[Type],
    rhs: Expr,
    _firstToken: TokenIdx,
)


impl Tokens[LetStmt]:
    firstToken(self: LetStmt) TokenIdx:
        self._firstToken

    lastToken(self: LetStmt) TokenIdx:
        self.rhs.lastToken()


#[derive(ToDoc)]
type AssignStmt(
    lhs: Expr,
    rhs: Expr,
    op: AssignOp,
)


impl Tokens[AssignStmt]:
    firstToken(self: AssignStmt) TokenIdx:
        self.lhs.firstToken()

    lastToken(self: AssignStmt) TokenIdx:
        self.rhs.lastToken()


#[derive(ToDoc)]
type AssignOp:
    Eq
    PlusEq
    MinusEq
    StarEq
    CaretEq


#[derive(ToDoc)]
type ForStmt(
    label: Option[Id],
    pat: Pat,

    ## Type annotation on the loop variable, the `item` type in `Iterator[iter, item]`.
    astTy: Option[Type],

    ## `ast_ty`, converted to type checking types by the type checker.
    tcTy: Option[Type], # TODO: type-checking type


    expr: Expr,

    ## Filled in by the type checker: the iterator type. `iter` in `Iterator[iter, item]`.
    exprTy: Option[Type], # TODO: type-checking type


    body: Vec[Stmt],

    _firstToken: TokenIdx,
)


impl Tokens[ForStmt]:
    firstToken(self: ForStmt) TokenIdx:
        self._firstToken

    lastToken(self: ForStmt) TokenIdx:
        self.body.last().unwrap().lastToken()


#[derive(ToDoc)]
type WhileStmt(
    label: Option[Id],
    cond: Expr,
    body: Vec[Stmt],
    _firstToken: TokenIdx,
)


impl Tokens[WhileStmt]:
    firstToken(self: WhileStmt) TokenIdx:
        self._firstToken

    lastToken(self: WhileStmt) TokenIdx:
        self.body.last().unwrap().lastToken()


#[derive(ToDoc)]
type LoopStmt(
    body: Vec[Stmt],
    _firstToken: TokenIdx,
)


impl Tokens[LoopStmt]:
    firstToken(self: LoopStmt) TokenIdx:
        self._firstToken

    lastToken(self: LoopStmt) TokenIdx:
        self.body.last().unwrap().lastToken()


#[derive(ToDoc)]
type BreakStmt(
    label: Option[Id],

    ## How many levels of loops to break. Parser initializes this as 0, type checker updates
    ## based on the labels of enclosing loops.
    level: U32,

    _firstToken: TokenIdx,
)


impl Tokens[BreakStmt]:
    firstToken(self: BreakStmt) TokenIdx:
        self._firstToken

    lastToken(self: BreakStmt) TokenIdx:
        match self.label:
            Option.Some(id): id.lastToken()
            Option.None: self._firstToken


#[derive(ToDoc)]
type ContinueStmt(
    label: Option[Id],

    ## Same as `BreakStmt.level`.
    level: U32,

    _firstToken: TokenIdx,
)


impl Tokens[ContinueStmt]:
    firstToken(self: ContinueStmt) TokenIdx:
        self._firstToken

    lastToken(self: ContinueStmt) TokenIdx:
        match self.label:
            Option.Some(id): id.lastToken()
            Option.None: self._firstToken


#[derive(ToDoc)]
type Pat:
    ## Matches anything, binds it to variable.
    Var(VarPat)

    ## Matches a constructor.
    Constr(ConstrPat)

    Record(RecordPat)

    ## Underscore, aka. wildcard.
    Ignore(TokenIdx)

    ## Matches the string.
    Str(Str, TokenIdx)

    ## Matches the character.
    Char(Char, TokenIdx)

    ## Or pattern: `<pat1> | <pat2> | ...`. At least two patterns.
    Or(Vec[Pat])


impl Tokens[Pat]:
    firstToken(self: Pat) TokenIdx:
        match self:
            Pat.Var(pat): pat.firstToken()

            Pat.Constr(pat): pat.firstToken()

            Pat.Record(pat): pat.firstToken()

            Pat.Ignore(tok) | Pat.Str(_, tok) | Pat.Char(_, tok): tok

            Pat.Or(ps): ps.get(0).firstToken()

    lastToken(self: Pat) TokenIdx:
        match self:
            Pat.Var(pat): pat.lastToken()

            Pat.Constr(pat): pat.lastToken()

            Pat.Record(pat): pat.lastToken()

            Pat.Ignore(tok) | Pat.Str(_, tok) | Pat.Char(_, tok): tok

            Pat.Or(ps): ps.last().unwrap().lastToken()


#[derive(ToDoc)]
type VarPat(
    var_: Id,

    ## Inferred type of the binder. Filled in by the type checker.
    ty: Option[Type], # TODO: This should be type-checking type instead of AST type

)


impl Tokens[VarPat]:
    firstToken(self: VarPat) TokenIdx:
        self.var_.firstToken()

    lastToken(self: VarPat) TokenIdx:
        self.var_.lastToken()


#[derive(ToDoc)]
type ConstrPat(
    constr: Constructor,
    fields: Vec[Named[Pat]],
    ignoreRest: Bool,
    _lastToken: TokenIdx,
)


impl Tokens[ConstrPat]:
    firstToken(self: ConstrPat) TokenIdx:
        self.constr.firstToken()

    lastToken(self: ConstrPat) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type RecordPat(
    fields: Vec[Named[Pat]],
    ignoreRest: Bool,

    # TODO: This should be type-checking type instead of AST type
    inferredTy: Option[Type],
    _firstToken: TokenIdx,
    _lastToken: TokenIdx,
)


impl Tokens[RecordPat]:
    firstToken(self: RecordPat) TokenIdx:
        self._firstToken

    lastToken(self: RecordPat) TokenIdx:
        self._lastToken


## A sum or product constructor, in patterns and expressions.
#[derive(ToDoc)]
type Constructor(
    variant: Bool,

    ## Type of the constructor.
    ty: TyId,

    ## Name of the constructor. Only in sum types.
    constr: Option[Id],

    ## Type arguments explicitly passed to the variable.
    ##
    ## Always `Option.None` in patterns.
    userTyArgs: Option[TyArgs],

    ## Inferred type arguments of the constructor's type. Filled in by the type checker.
    tyArgs: Vec[Type],

    # In variant constructors we'll see a '~' before `ty`, so we can't use `ty` as the first token.
    _firstToken: TokenIdx,
)


impl Tokens[Constructor]:
    firstToken(self: Constructor) TokenIdx:
        self._firstToken

    lastToken(self: Constructor) TokenIdx:
        match self.userTyArgs:
            Option.Some(tyArgs): tyArgs.lastToken()
            Option.None:
                match self.constr:
                    Option.Some(con): con.token
                    Option.None: self.ty.token


#[derive(ToDoc)]
type Expr:
    ## A variable: `x`.
    Var(VarExpr)

    ## A constructor: `Option.None`, `Result.Ok`, `Bool.True`, `Vec`.
    ConstrSelect(Constructor)

    ## A field selection: `<expr>.x` where `x` is a field.
    ##
    ## Parser generates this node for all expression of form `<expr>.<id>`, type checker converts
    ## method selection expressions to `MethodSelect`.
    FieldSelect(FieldSelectExpr)

    ## A method selection: `<expr>.x` where `x` is a method.
    ##
    ## This node is generated by the type checker.
    MethodSelect(MethodSelectExpr)

    ## An associated function or method selection:
    ##
    ## - Associated function: `Vec.withCapacity`.
    ## - Method: `Vec.push`.
    AssocFnSelect(AssocFnSelectExpr)

    ## A function call: `f(a)`.
    Call(CallExpr)

    ## An integer literal.
    Int(IntExpr)

    ## A string literal.
    Str(StrExpr)

    ## A character literal.
    Char(CharExpr)

    Self(TokenIdx)

    ## A binary operator: `x + y`, `i >> 2`.
    ##
    ## Some of the binary operators are desugared to method calls by the type checker.
    BinOp(BinOpExpr)

    ## A unary operator: `-x`, `!b`.
    ##
    ## Some of the unary operators are desugared to method calls by the type checker.
    UnOp(UnOpExpr)

    ## A record: `(1, 2)`, `(x = 123, msg = "hi")`.
    Record(RecordExpr)

    Return(ReturnExpr)

    Match(MatchExpr)

    If(IfExpr)

    Fn_(FnExpr)

    Is(IsExpr)

    Do(DoExpr)

    # A sequence: `[a, b, c]`, `[a = b, c = d]`, `Vec.[...]`. Can be empty.
    Seq(SeqExpr)

    # A parenthesized expression.
    Paren(ParenExpr)


impl Tokens[Expr]:
    firstToken(self: Expr) TokenIdx:
        match self:
            Expr.Var(e): e.firstToken()
            Expr.ConstrSelect(e): e.firstToken()
            Expr.FieldSelect(e): e.firstToken()
            Expr.MethodSelect(e): e.firstToken()
            Expr.AssocFnSelect(e): e.firstToken()
            Expr.Call(e): e.firstToken()
            Expr.Int(e): e.firstToken()
            Expr.Str(e): e.firstToken()
            Expr.Char(e): e.firstToken()
            Expr.Self(t): t
            Expr.BinOp(e): e.firstToken()
            Expr.UnOp(e): e.firstToken()
            Expr.Record(e): e.firstToken()
            Expr.Return(e): e.firstToken()
            Expr.Match(e): e.firstToken()
            Expr.If(e): e.firstToken()
            Expr.Fn_(e): e.firstToken()
            Expr.Is(e): e.firstToken()
            Expr.Do(e): e.firstToken()
            Expr.Seq(e): e.firstToken()
            Expr.Paren(e): e.firstToken()

    lastToken(self: Expr) TokenIdx:
        match self:
            Expr.Var(e): e.lastToken()
            Expr.ConstrSelect(e): e.lastToken()
            Expr.FieldSelect(e): e.lastToken()
            Expr.MethodSelect(e): e.lastToken()
            Expr.AssocFnSelect(e): e.lastToken()
            Expr.Call(e): e.lastToken()
            Expr.Int(e): e.lastToken()
            Expr.Str(e): e.lastToken()
            Expr.Char(e): e.lastToken()
            Expr.Self(t): t
            Expr.BinOp(e): e.lastToken()
            Expr.UnOp(e): e.lastToken()
            Expr.Record(e): e.lastToken()
            Expr.Return(e): e.lastToken()
            Expr.Match(e): e.lastToken()
            Expr.If(e): e.lastToken()
            Expr.Fn_(e): e.lastToken()
            Expr.Is(e): e.lastToken()
            Expr.Do(e): e.lastToken()
            Expr.Seq(e): e.lastToken()
            Expr.Paren(e): e.lastToken()


#[derive(ToDoc)]
type VarExpr(
    id: VarId,

    # Type arguments explicitly passed to the variable.
    userTyArgs: Option[TyArgs],

    ## Inferred type arguments of the variable. Filled in by the type checker.
    tyArgs: Vec[Type],
)


impl Tokens[VarExpr]:
    firstToken(self: VarExpr) TokenIdx:
        self.id.token

    lastToken(self: VarExpr) TokenIdx:
        match self.userTyArgs:
            Option.Some(tyArgs): tyArgs.lastToken()
            Option.None: self.id.token


#[derive(ToDoc)]
type TyArgs(
    args: Vec[Type],

    # Left bracket.
    _firstToken: TokenIdx,

    # Right bracket.
    _lastToken: TokenIdx,
)


impl Tokens[TyArgs]:
    firstToken(self: TyArgs) TokenIdx:
        self._firstToken

    lastToken(self: TyArgs) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type FieldSelectExpr(
    object: Expr,

    field: Id,

    ## Type arguments explicitly passed to the variable.
    ##
    ## Since fields can't have `forall` quantifiers, this will only be valid when the field is a
    ## method, in which case the type checker will convert this node into `MethodSelectExpr`.
    userTyArgs: Option[TyArgs],
)


impl Tokens[FieldSelectExpr]:
    firstToken(self: FieldSelectExpr) TokenIdx:
        self.object.firstToken()

    lastToken(self: FieldSelectExpr) TokenIdx:
        match self.userTyArgs:
            Option.Some(tyArgs): tyArgs.lastToken()
            Option.None: self.field.lastToken()


## A method selection: `<expr>.method`.
##
## This node is generated by the type checker, from `Expr::FieldSelect`.
##
## Methods are always associated functions. They can be associated to a type (e.g. `Vec.push`) or
## trait methods (e.g. `Iterator.next`).
#[derive(ToDoc)]
type MethodSelectExpr(
    ## The reciever, `<expr>` in `<expr>.method`.
    object: Expr,

    ## Type of `object` (receiver), filled in by the type checker.
    ##
    ## This type will always be a type constructor, potentially with arguments, as types without
    ## type constructors (records etc.) don't have methods.
    ##
    ## The type constructor will be the type with the associated function with `method` as the name
    ## and a `self` parameter that matches this type.
    # TODO: We could have separate fields for the ty con and args.
    # TODO: We could also add types to every expression if it's going to help with monomorphisation.
    #       For efficiency though, we should only annotate inferred types and then type check from
    #       the top-level expression every time we need to compute type of an expr.
    # TODO: This should be a type-checking type.
    objectTy: Option[Type],

    ## The type or trait id that defines the method.
    ##
    ## E.g. `Vec`, `Iterator`.
    ##
    ## Note: when calling trait methods, this will be the trait type rather than the receiver type.
    methodTyId: TyId,

    ## The method id.
    ##
    ## E.g. `push`, `next`.
    method: AssocVarId,

    ## Type arguments of `method_ty_id`.
    ##
    ## If the method is for a trait, the first arguments here will be for the trait type parameters.
    ## E.g. in `Iterator.next`, the first two argumetns will be the `iter` and `item` parameters of
    ## `trait Iterator[iter, item]`.
    ##
    ## (If the method is not a trait method, then we don't care about the type parameter order.. I
    ## think?)
    tyArgs: Vec[Type], # TODO: type-checking type


    _lastToken: TokenIdx,
)


impl Tokens[MethodSelectExpr]:
    firstToken(self: MethodSelectExpr) TokenIdx:
        self.object.firstToken()

    lastToken(self: MethodSelectExpr) TokenIdx:
        self._lastToken


## An associated function or method selection:
##
## - Associated function: `Vec.withCapacity`.
## - Method: `Vec.push`.
#[derive(ToDoc)]
type AssocFnSelectExpr(
    # The type of the associated function: `Vec` in the examples above.
    ty: TyId,

    # The associated function name: `withCapacity` and `push` in the examples
    # above.
    member: AssocVarId,

    ## Type arguments explicitly passed to the variable.
    userTyArgs: Option[TyArgs],

    ## Inferred type arguments of the type and associated function. Filled in by the type checker.
    tyArgs: Vec[Type], # TODO: type-checking type


    _lastToken: TokenIdx,
)


impl Tokens[AssocFnSelectExpr]:
    firstToken(self: AssocFnSelectExpr) TokenIdx:
        self.ty.token

    lastToken(self: AssocFnSelectExpr) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type CallExpr(
    fun: Expr,
    args: Vec[Named[Expr]],
    _lastToken: TokenIdx,
)


impl Tokens[CallExpr]:
    firstToken(self: CallExpr) TokenIdx:
        self.fun.firstToken()

    lastToken(self: CallExpr) TokenIdx:
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
    firstToken(self: IntExpr) TokenIdx:
        self.token

    lastToken(self: IntExpr) TokenIdx:
        self.token


#[derive(ToDoc)]
type StrExpr(
    parts: Vec[StrPart],
    token: TokenIdx,
)


impl Tokens[StrExpr]:
    firstToken(self: StrExpr) TokenIdx:
        self.token

    lastToken(self: StrExpr) TokenIdx:
        self.token


#[derive(ToDoc)]
type StrPart:
    Str(Str)
    Expr(Expr)


#[derive(ToDoc)]
type CharExpr(
    char: Char,
    token: TokenIdx,
)


impl Tokens[CharExpr]:
    firstToken(self: CharExpr) TokenIdx:
        self.token

    lastToken(self: CharExpr) TokenIdx:
        self.token


#[derive(ToDoc)]
type BinOpExpr(
    left: Expr,
    right: Expr,
    op: BinOp,
)


impl Tokens[BinOpExpr]:
    firstToken(self: BinOpExpr) TokenIdx:
        self.left.firstToken()

    lastToken(self: BinOpExpr) TokenIdx:
        self.right.lastToken()


#[derive(ToDoc)]
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
type UnOpExpr(
    op: UnOp,
    expr: Expr,
    _firstToken: TokenIdx,
)


impl Tokens[UnOpExpr]:
    firstToken(self: UnOpExpr) TokenIdx:
        self._firstToken

    lastToken(self: UnOpExpr) TokenIdx:
        self.expr.lastToken()


#[derive(ToDoc)]
type RecordExpr(
    fields: Vec[Named[Expr]],
    _firstToken: TokenIdx,
    _lastToken: TokenIdx,
)


impl Tokens[RecordExpr]:
    firstToken(self: RecordExpr) TokenIdx:
        self._firstToken

    lastToken(self: RecordExpr) TokenIdx:
        self._lastToken


#[derive(ToDoc)]
type ReturnExpr(
    expr: Option[Expr],
    _firstToken: TokenIdx,
)


impl Tokens[ReturnExpr]:
    firstToken(self: ReturnExpr) TokenIdx:
        self._firstToken

    lastToken(self: ReturnExpr) TokenIdx:
        match self.expr:
            Option.Some(expr): expr.lastToken()
            Option.None: self._firstToken


#[derive(ToDoc)]
type MatchExpr(
    scrutinee: Expr,
    alts: Vec[Alt],
    _firstToken: TokenIdx,
)


impl Tokens[MatchExpr]:
    firstToken(self: MatchExpr) TokenIdx:
        self._firstToken

    lastToken(self: MatchExpr) TokenIdx:
        self.alts.last().unwrap().lastToken()


#[derive(ToDoc)]
type Alt(
    pattern: Pat,
    guard: Option[Expr],
    rhs: Vec[Stmt],
)


impl Tokens[Alt]:
    firstToken(self: Alt) TokenIdx:
        self.pattern.firstToken()

    lastToken(self: Alt) TokenIdx:
        self.rhs.last().unwrap().lastToken()


#[derive(ToDoc)]
type IfExpr(
    # At least one element
    branches: Vec[IfBranch],
    elseBranch: Option[Vec[Stmt]],
    _firstToken: TokenIdx,
)


#[derive(ToDoc)]
type IfBranch(
    guard: Expr,
    body: Vec[Stmt],
)


impl Tokens[IfExpr]:
    firstToken(self: IfExpr) TokenIdx:
        self._firstToken

    lastToken(self: IfExpr) TokenIdx:
        if self.elseBranch is Option.Some(block):
            return block.last().unwrap().lastToken()

        self.branches.last().unwrap().body.last().unwrap().lastToken()


#[derive(ToDoc)]
type FnExpr(
    sig: FunSig,
    body: Vec[Stmt],
    idx: U32,
    _firstToken: TokenIdx,
)


impl Tokens[FnExpr]:
    firstToken(self: FnExpr) TokenIdx:
        self._firstToken

    lastToken(self: FnExpr) TokenIdx:
        self.body.last().unwrap().lastToken()


# <expr> is <pat>
#[derive(ToDoc)]
type IsExpr(
    expr: Expr,
    pat: Pat,
)


impl Tokens[IsExpr]:
    firstToken(self: IsExpr) TokenIdx:
        self.expr.firstToken()

    lastToken(self: IsExpr) TokenIdx:
        self.pat.lastToken()


#[derive(ToDoc)]
type DoExpr(
    body: Vec[Stmt],
    _firstToken: TokenIdx,
)


impl Tokens[DoExpr]:
    firstToken(self: DoExpr) TokenIdx:
        self._firstToken

    lastToken(self: DoExpr) TokenIdx:
        self.body.last().unwrap().lastToken()


#[derive(ToDoc)]
type UnOp:
    Not
    Neg


#[derive(ToDoc)]
type SeqExpr(
    ty: Option[Type],
    elems: Vec[SeqElem],
    _lbracket: TokenIdx,
    _rbracket: TokenIdx,
)


#[derive(ToDoc)]
type SeqElem(
    key: Option[Expr],
    value: Expr,
)


impl Tokens[SeqExpr]:
    firstToken(self: SeqExpr) TokenIdx:
        match self.ty:
            Option.Some(ty): ty.firstToken()
            Option.None: self._lbracket

    lastToken(self: SeqExpr) TokenIdx:
        self._rbracket


#[derive(ToDoc)]
type ParenExpr(
    expr: Expr,
    _lparen: TokenIdx,
    _rparen: TokenIdx,
)


impl Tokens[ParenExpr]:
    firstToken(self: ParenExpr) TokenIdx:
        self._lparen

    lastToken(self: ParenExpr) TokenIdx:
        self._rparen


# --------------------------------------------------------------------------------------------------


impl ToStr[BinOp]:
    toStr(self: BinOp) Str:
        match self:
            BinOp.Add: "Add"
            BinOp.And: "And"
            BinOp.BitAnd: "BitAnd"
            BinOp.BitOr: "BitOr"
            BinOp.Divide: "Divide"
            BinOp.Equal: "Equal"
            BinOp.Gt: "Gt"
            BinOp.GtEq: "GtEq"
            BinOp.LeftShift: "LeftShift"
            BinOp.Lt: "Lt"
            BinOp.LtEq: "LtEq"
            BinOp.Multiply: "Multiply"
            BinOp.NotEqual: "NotEqual"
            BinOp.Or: "Or"
            BinOp.RightShift: "RightShift"
            BinOp.Subtract: "Subtract"


impl Eq[BinOp]:
    __eq(self: BinOp, other: BinOp) Bool:
        match (left = self, right = other):
            (left = BinOp.Add, right = BinOp.Add): Bool.True
            (left = BinOp.And, right = BinOp.And): Bool.True
            (left = BinOp.BitAnd, right = BinOp.BitOr): Bool.True
            (left = BinOp.Divide, right = BinOp.Divide): Bool.True
            (left = BinOp.Equal, right = BinOp.Equal): Bool.True
            (left = BinOp.Gt, right = BinOp.Gt): Bool.True
            (left = BinOp.GtEq, right = BinOp.GtEq): Bool.True
            (left = BinOp.LeftShift, right = BinOp.LeftShift): Bool.True
            (left = BinOp.Lt, right = BinOp.Lt): Bool.True
            (left = BinOp.LtEq, right = BinOp.LtEq): Bool.True
            (left = BinOp.Multiply, right = BinOp.Multiply): Bool.True
            (left = BinOp.NotEqual, right = BinOp.NotEqual): Bool.True
            (left = BinOp.Or, right = BinOp.Or): Bool.True
            (left = BinOp.RightShift, right = BinOp.RightShift): Bool.True
            (left = BinOp.Subtract, right = BinOp.Subtract): Bool.True
            _: Bool.False


# --------------------------------------------------------------------------------------------------
# Implementations below are generated with `Compiler/DeriveToDoc`, do not edit.


impl ToDoc[TokenIdx]:
    toDoc(self: TokenIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("idx =") + Doc.nested(4, Doc.break_(1) + self.idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TokenIdx") + Doc.char('(') + args)


impl ToDoc[Id]:
    toDoc(self: Id) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("token =")
                + Doc.nested(4, Doc.break_(1) + self.token.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Id") + Doc.char('(') + args)


impl ToDoc[TopDecl]:
    toDoc(self: TopDecl) Doc:
        match self:
            TopDecl.Type(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TopDecl.Type") + Doc.char('(') + args)
            TopDecl.Fun(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TopDecl.Fun") + Doc.char('(') + args)
            TopDecl.Import(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TopDecl.Import") + Doc.char('(') + args)
            TopDecl.Trait(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TopDecl.Trait") + Doc.char('(') + args)
            TopDecl.Impl(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TopDecl.Impl") + Doc.char('(') + args)


impl ToDoc[TypeDecl]:
    toDoc(self: TypeDecl) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("prim_ =")
                + Doc.nested(4, Doc.break_(1) + self.prim_.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("typeParams =")
                + Doc.nested(4, Doc.break_(1) + self.typeParams.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("typeParamKinds =")
                + Doc.nested(4, Doc.break_(1) + self.typeParamKinds.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("rhs =") + Doc.nested(4, Doc.break_(1) + self.rhs.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TypeDecl") + Doc.char('(') + args)


impl ToDoc[TypeDeclRhs]:
    toDoc(self: TypeDeclRhs) Doc:
        match self:
            TypeDeclRhs.Sum(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TypeDeclRhs.Sum") + Doc.char('(') + args)
            TypeDeclRhs.Product(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(
                    Doc.str("TypeDeclRhs.Product") + Doc.char('(') + args,
                )


impl ToDoc[ConDecl]:
    toDoc(self: ConDecl) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("fields =")
                + Doc.nested(4, Doc.break_(1) + self.fields.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ConDecl") + Doc.char('(') + args)


impl ToDoc[Kind]:
    toDoc(self: Kind) Doc:
        match self:
            Kind.Star: Doc.str("Kind.Star")
            Kind.Row(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Kind.Row") + Doc.char('(') + args)


impl ToDoc[RecordOrVariant]:
    toDoc(self: RecordOrVariant) Doc:
        match self:
            RecordOrVariant.Record: Doc.str("RecordOrVariant.Record")
            RecordOrVariant.Variant: Doc.str("RecordOrVariant.Variant")


impl ToDoc[ConFields]:
    toDoc(self: ConFields) Doc:
        match self:
            ConFields.Empty: Doc.str("ConFields.Empty")
            ConFields.Named(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("ConFields.Named") + Doc.char('(') + args)
            ConFields.Unnamed(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("ConFields.Unnamed") + Doc.char('(') + args)


impl ToDoc[NamedField]:
    toDoc(self: NamedField) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("NamedField") + Doc.char('(') + args)


impl ToDoc[FunDecl]:
    toDoc(self: FunDecl) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("prim_ =")
                + Doc.nested(4, Doc.break_(1) + self.prim_.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("parentTy =")
                + Doc.nested(4, Doc.break_(1) + self.parentTy.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("sig =") + Doc.nested(4, Doc.break_(1) + self.sig.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("body =") + Doc.nested(4, Doc.break_(1) + self.body.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("FunDecl") + Doc.char('(') + args)


impl ToDoc[FunSig]:
    toDoc(self: FunSig) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("context =")
                + Doc.nested(4, Doc.break_(1) + self.context.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("self_ =")
                + Doc.nested(4, Doc.break_(1) + self.self_.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("params =")
                + Doc.nested(4, Doc.break_(1) + self.params.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("exceptions =")
                + Doc.nested(4, Doc.break_(1) + self.exceptions.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("returnTy =")
                + Doc.nested(4, Doc.break_(1) + self.returnTy.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("FunSig") + Doc.char('(') + args)


impl ToDoc[FunArg]:
    toDoc(self: FunArg) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("FunArg") + Doc.char('(') + args)


impl ToDoc[SelfParam]:
    toDoc(self: SelfParam) Doc:
        match self:
            SelfParam.No: Doc.str("SelfParam.No")
            SelfParam.Implicit: Doc.str("SelfParam.Implicit")
            SelfParam.Explicit(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("SelfParam.Explicit") + Doc.char('(') + args)


impl ToDoc[ImportDecl]:
    toDoc(self: ImportDecl) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("paths =")
                + Doc.nested(4, Doc.break_(1) + self.paths.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ImportDecl") + Doc.char('(') + args)


impl ToDoc[TraitDecl]:
    toDoc(self: TraitDecl) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("typeParams =")
                + Doc.nested(4, Doc.break_(1) + self.typeParams.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("typeParamKinds =")
                + Doc.nested(4, Doc.break_(1) + self.typeParamKinds.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("items =")
                + Doc.nested(4, Doc.break_(1) + self.items.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TraitDecl") + Doc.char('(') + args)


impl ToDoc[ImplDecl]:
    toDoc(self: ImplDecl) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("context =")
                + Doc.nested(4, Doc.break_(1) + self.context.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("trait_ =")
                + Doc.nested(4, Doc.break_(1) + self.trait_.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("tys =") + Doc.nested(4, Doc.break_(1) + self.tys.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("items =")
                + Doc.nested(4, Doc.break_(1) + self.items.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ImplDecl") + Doc.char('(') + args)


impl ToDoc[Type]:
    toDoc(self: Type) Doc:
        match self:
            Type.Named(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Type.Named") + Doc.char('(') + args)
            Type.Var(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Type.Var") + Doc.char('(') + args)
            Type.Record(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Type.Record") + Doc.char('(') + args)
            Type.Variant(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Type.Variant") + Doc.char('(') + args)
            Type.Fn_(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Type.Fn_") + Doc.char('(') + args)


impl ToDoc[RecordType]:
    toDoc(self: RecordType) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("fields =")
                + Doc.nested(4, Doc.break_(1) + self.fields.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("extension =")
                + Doc.nested(4, Doc.break_(1) + self.extension.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("isRow =")
                + Doc.nested(4, Doc.break_(1) + self.isRow.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("RecordType") + Doc.char('(') + args)


impl ToDoc[VariantType]:
    toDoc(self: VariantType) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("alts =") + Doc.nested(4, Doc.break_(1) + self.alts.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("extension =")
                + Doc.nested(4, Doc.break_(1) + self.extension.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("isRow =")
                + Doc.nested(4, Doc.break_(1) + self.isRow.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("VariantType") + Doc.char('(') + args)


impl ToDoc[FnType]:
    toDoc(self: FnType) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("args =") + Doc.nested(4, Doc.break_(1) + self.args.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ret =") + Doc.nested(4, Doc.break_(1) + self.ret.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("exceptions =")
                + Doc.nested(4, Doc.break_(1) + self.exceptions.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_rparen =")
                + Doc.nested(4, Doc.break_(1) + self._rparen.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("FnType") + Doc.char('(') + args)


impl ToDoc[Context]:
    toDoc(self: Context) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("typeParams =")
                + Doc.nested(4, Doc.break_(1) + self.typeParams.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("preds =")
                + Doc.nested(4, Doc.break_(1) + self.preds.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Context") + Doc.char('(') + args)


impl ToDoc[TypeParam]:
    toDoc(self: TypeParam) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("kind =") + Doc.nested(4, Doc.break_(1) + self.kind.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TypeParam") + Doc.char('(') + args)


impl ToDoc[NamedType]:
    toDoc(self: NamedType) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("args =") + Doc.nested(4, Doc.break_(1) + self.args.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("NamedType") + Doc.char('(') + args)


impl[ToDoc[t]] ToDoc[Named[t]]:
    toDoc(self: Named[t]) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("node =") + Doc.nested(4, Doc.break_(1) + self.node.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Named") + Doc.char('(') + args)


impl ToDoc[Stmt]:
    toDoc(self: Stmt) Doc:
        match self:
            Stmt.Let(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.Let") + Doc.char('(') + args)
            Stmt.Assign(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.Assign") + Doc.char('(') + args)
            Stmt.Expr(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.Expr") + Doc.char('(') + args)
            Stmt.For(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.For") + Doc.char('(') + args)
            Stmt.While(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.While") + Doc.char('(') + args)
            Stmt.Loop(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.Loop") + Doc.char('(') + args)
            Stmt.Break(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.Break") + Doc.char('(') + args)
            Stmt.Continue(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Stmt.Continue") + Doc.char('(') + args)


impl ToDoc[LetStmt]:
    toDoc(self: LetStmt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("lhs =") + Doc.nested(4, Doc.break_(1) + self.lhs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("rhs =") + Doc.nested(4, Doc.break_(1) + self.rhs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("LetStmt") + Doc.char('(') + args)


impl ToDoc[AssignStmt]:
    toDoc(self: AssignStmt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("lhs =") + Doc.nested(4, Doc.break_(1) + self.lhs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("rhs =") + Doc.nested(4, Doc.break_(1) + self.rhs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("op =") + Doc.nested(4, Doc.break_(1) + self.op.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("AssignStmt") + Doc.char('(') + args)


impl ToDoc[AssignOp]:
    toDoc(self: AssignOp) Doc:
        match self:
            AssignOp.Eq: Doc.str("AssignOp.Eq")
            AssignOp.PlusEq: Doc.str("AssignOp.PlusEq")
            AssignOp.MinusEq: Doc.str("AssignOp.MinusEq")
            AssignOp.StarEq: Doc.str("AssignOp.StarEq")
            AssignOp.CaretEq: Doc.str("AssignOp.CaretEq")


impl ToDoc[ForStmt]:
    toDoc(self: ForStmt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("label =")
                + Doc.nested(4, Doc.break_(1) + self.label.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("pat =") + Doc.nested(4, Doc.break_(1) + self.pat.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("astTy =")
                + Doc.nested(4, Doc.break_(1) + self.astTy.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("tcTy =") + Doc.nested(4, Doc.break_(1) + self.tcTy.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("expr =") + Doc.nested(4, Doc.break_(1) + self.expr.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("exprTy =")
                + Doc.nested(4, Doc.break_(1) + self.exprTy.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("body =") + Doc.nested(4, Doc.break_(1) + self.body.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ForStmt") + Doc.char('(') + args)


impl ToDoc[WhileStmt]:
    toDoc(self: WhileStmt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("label =")
                + Doc.nested(4, Doc.break_(1) + self.label.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("cond =") + Doc.nested(4, Doc.break_(1) + self.cond.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("body =") + Doc.nested(4, Doc.break_(1) + self.body.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("WhileStmt") + Doc.char('(') + args)


impl ToDoc[LoopStmt]:
    toDoc(self: LoopStmt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("body =") + Doc.nested(4, Doc.break_(1) + self.body.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("LoopStmt") + Doc.char('(') + args)


impl ToDoc[BreakStmt]:
    toDoc(self: BreakStmt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("label =")
                + Doc.nested(4, Doc.break_(1) + self.label.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("level =")
                + Doc.nested(4, Doc.break_(1) + self.level.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("BreakStmt") + Doc.char('(') + args)


impl ToDoc[ContinueStmt]:
    toDoc(self: ContinueStmt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("label =")
                + Doc.nested(4, Doc.break_(1) + self.label.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("level =")
                + Doc.nested(4, Doc.break_(1) + self.level.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ContinueStmt") + Doc.char('(') + args)


impl ToDoc[Pat]:
    toDoc(self: Pat) Doc:
        match self:
            Pat.Var(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Pat.Var") + Doc.char('(') + args)
            Pat.Constr(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Pat.Constr") + Doc.char('(') + args)
            Pat.Record(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Pat.Record") + Doc.char('(') + args)
            Pat.Ignore(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Pat.Ignore") + Doc.char('(') + args)
            Pat.Str(i0, i1):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args += Doc.char(',') + Doc.break_(1)
                args += i1.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Pat.Str") + Doc.char('(') + args)
            Pat.Char(i0, i1):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args += Doc.char(',') + Doc.break_(1)
                args += i1.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Pat.Char") + Doc.char('(') + args)
            Pat.Or(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Pat.Or") + Doc.char('(') + args)


impl ToDoc[VarPat]:
    toDoc(self: VarPat) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("var_ =") + Doc.nested(4, Doc.break_(1) + self.var_.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("VarPat") + Doc.char('(') + args)


impl ToDoc[ConstrPat]:
    toDoc(self: ConstrPat) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("constr =")
                + Doc.nested(4, Doc.break_(1) + self.constr.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("fields =")
                + Doc.nested(4, Doc.break_(1) + self.fields.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ignoreRest =")
                + Doc.nested(4, Doc.break_(1) + self.ignoreRest.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ConstrPat") + Doc.char('(') + args)


impl ToDoc[RecordPat]:
    toDoc(self: RecordPat) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("fields =")
                + Doc.nested(4, Doc.break_(1) + self.fields.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ignoreRest =")
                + Doc.nested(4, Doc.break_(1) + self.ignoreRest.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("inferredTy =")
                + Doc.nested(4, Doc.break_(1) + self.inferredTy.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("RecordPat") + Doc.char('(') + args)


impl ToDoc[Constructor]:
    toDoc(self: Constructor) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("variant =")
                + Doc.nested(4, Doc.break_(1) + self.variant.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("constr =")
                + Doc.nested(4, Doc.break_(1) + self.constr.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("userTyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.userTyArgs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("tyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.tyArgs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Constructor") + Doc.char('(') + args)


impl ToDoc[Expr]:
    toDoc(self: Expr) Doc:
        match self:
            Expr.Var(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Var") + Doc.char('(') + args)
            Expr.ConstrSelect(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.ConstrSelect") + Doc.char('(') + args)
            Expr.FieldSelect(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.FieldSelect") + Doc.char('(') + args)
            Expr.MethodSelect(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.MethodSelect") + Doc.char('(') + args)
            Expr.AssocFnSelect(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.AssocFnSelect") + Doc.char('(') + args)
            Expr.Call(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Call") + Doc.char('(') + args)
            Expr.Int(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Int") + Doc.char('(') + args)
            Expr.Str(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Str") + Doc.char('(') + args)
            Expr.Char(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Char") + Doc.char('(') + args)
            Expr.Self(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Self") + Doc.char('(') + args)
            Expr.BinOp(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.BinOp") + Doc.char('(') + args)
            Expr.UnOp(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.UnOp") + Doc.char('(') + args)
            Expr.Record(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Record") + Doc.char('(') + args)
            Expr.Return(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Return") + Doc.char('(') + args)
            Expr.Match(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Match") + Doc.char('(') + args)
            Expr.If(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.If") + Doc.char('(') + args)
            Expr.Fn_(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Fn_") + Doc.char('(') + args)
            Expr.Is(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Is") + Doc.char('(') + args)
            Expr.Do(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Do") + Doc.char('(') + args)
            Expr.Seq(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Seq") + Doc.char('(') + args)
            Expr.Paren(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Expr.Paren") + Doc.char('(') + args)


impl ToDoc[VarExpr]:
    toDoc(self: VarExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("id =") + Doc.nested(4, Doc.break_(1) + self.id.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("userTyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.userTyArgs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("tyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.tyArgs.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("VarExpr") + Doc.char('(') + args)


impl ToDoc[TyArgs]:
    toDoc(self: TyArgs) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("args =") + Doc.nested(4, Doc.break_(1) + self.args.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TyArgs") + Doc.char('(') + args)


impl ToDoc[FieldSelectExpr]:
    toDoc(self: FieldSelectExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("object =")
                + Doc.nested(4, Doc.break_(1) + self.object.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("field =")
                + Doc.nested(4, Doc.break_(1) + self.field.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("userTyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.userTyArgs.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("FieldSelectExpr") + Doc.char('(') + args)


impl ToDoc[MethodSelectExpr]:
    toDoc(self: MethodSelectExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("object =")
                + Doc.nested(4, Doc.break_(1) + self.object.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("objectTy =")
                + Doc.nested(4, Doc.break_(1) + self.objectTy.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("methodTyId =")
                + Doc.nested(4, Doc.break_(1) + self.methodTyId.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("method =")
                + Doc.nested(4, Doc.break_(1) + self.method.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("tyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.tyArgs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("MethodSelectExpr") + Doc.char('(') + args)


impl ToDoc[AssocFnSelectExpr]:
    toDoc(self: AssocFnSelectExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("member =")
                + Doc.nested(4, Doc.break_(1) + self.member.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("userTyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.userTyArgs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("tyArgs =")
                + Doc.nested(4, Doc.break_(1) + self.tyArgs.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("AssocFnSelectExpr") + Doc.char('(') + args)


impl ToDoc[CallExpr]:
    toDoc(self: CallExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("fun =") + Doc.nested(4, Doc.break_(1) + self.fun.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("args =") + Doc.nested(4, Doc.break_(1) + self.args.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("CallExpr") + Doc.char('(') + args)


impl ToDoc[IntExpr]:
    toDoc(self: IntExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("text =") + Doc.nested(4, Doc.break_(1) + self.text.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("suffix =")
                + Doc.nested(4, Doc.break_(1) + self.suffix.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("radix =")
                + Doc.nested(4, Doc.break_(1) + self.radix.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("parsed =")
                + Doc.nested(4, Doc.break_(1) + self.parsed.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("token =")
                + Doc.nested(4, Doc.break_(1) + self.token.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("IntExpr") + Doc.char('(') + args)


impl ToDoc[StrExpr]:
    toDoc(self: StrExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("parts =")
                + Doc.nested(4, Doc.break_(1) + self.parts.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("token =")
                + Doc.nested(4, Doc.break_(1) + self.token.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("StrExpr") + Doc.char('(') + args)


impl ToDoc[StrPart]:
    toDoc(self: StrPart) Doc:
        match self:
            StrPart.Str(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("StrPart.Str") + Doc.char('(') + args)
            StrPart.Expr(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("StrPart.Expr") + Doc.char('(') + args)


impl ToDoc[CharExpr]:
    toDoc(self: CharExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("char =") + Doc.nested(4, Doc.break_(1) + self.char.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("token =")
                + Doc.nested(4, Doc.break_(1) + self.token.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("CharExpr") + Doc.char('(') + args)


impl ToDoc[BinOpExpr]:
    toDoc(self: BinOpExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("left =") + Doc.nested(4, Doc.break_(1) + self.left.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("right =")
                + Doc.nested(4, Doc.break_(1) + self.right.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("op =") + Doc.nested(4, Doc.break_(1) + self.op.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("BinOpExpr") + Doc.char('(') + args)


impl ToDoc[BinOp]:
    toDoc(self: BinOp) Doc:
        match self:
            BinOp.Add: Doc.str("BinOp.Add")
            BinOp.And: Doc.str("BinOp.And")
            BinOp.BitAnd: Doc.str("BinOp.BitAnd")
            BinOp.BitOr: Doc.str("BinOp.BitOr")
            BinOp.Divide: Doc.str("BinOp.Divide")
            BinOp.Equal: Doc.str("BinOp.Equal")
            BinOp.Gt: Doc.str("BinOp.Gt")
            BinOp.GtEq: Doc.str("BinOp.GtEq")
            BinOp.LeftShift: Doc.str("BinOp.LeftShift")
            BinOp.Lt: Doc.str("BinOp.Lt")
            BinOp.LtEq: Doc.str("BinOp.LtEq")
            BinOp.Multiply: Doc.str("BinOp.Multiply")
            BinOp.NotEqual: Doc.str("BinOp.NotEqual")
            BinOp.Or: Doc.str("BinOp.Or")
            BinOp.RightShift: Doc.str("BinOp.RightShift")
            BinOp.Subtract: Doc.str("BinOp.Subtract")


impl ToDoc[UnOpExpr]:
    toDoc(self: UnOpExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("op =") + Doc.nested(4, Doc.break_(1) + self.op.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("expr =") + Doc.nested(4, Doc.break_(1) + self.expr.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("UnOpExpr") + Doc.char('(') + args)


impl ToDoc[RecordExpr]:
    toDoc(self: RecordExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("fields =")
                + Doc.nested(4, Doc.break_(1) + self.fields.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lastToken =")
                + Doc.nested(4, Doc.break_(1) + self._lastToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("RecordExpr") + Doc.char('(') + args)


impl ToDoc[ReturnExpr]:
    toDoc(self: ReturnExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("expr =") + Doc.nested(4, Doc.break_(1) + self.expr.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ReturnExpr") + Doc.char('(') + args)


impl ToDoc[MatchExpr]:
    toDoc(self: MatchExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("scrutinee =")
                + Doc.nested(4, Doc.break_(1) + self.scrutinee.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("alts =") + Doc.nested(4, Doc.break_(1) + self.alts.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("MatchExpr") + Doc.char('(') + args)


impl ToDoc[Alt]:
    toDoc(self: Alt) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("pattern =")
                + Doc.nested(4, Doc.break_(1) + self.pattern.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("guard =")
                + Doc.nested(4, Doc.break_(1) + self.guard.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("rhs =") + Doc.nested(4, Doc.break_(1) + self.rhs.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Alt") + Doc.char('(') + args)


impl ToDoc[IfExpr]:
    toDoc(self: IfExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("branches =")
                + Doc.nested(4, Doc.break_(1) + self.branches.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("elseBranch =")
                + Doc.nested(4, Doc.break_(1) + self.elseBranch.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("IfExpr") + Doc.char('(') + args)


impl ToDoc[IfBranch]:
    toDoc(self: IfBranch) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("guard =")
                + Doc.nested(4, Doc.break_(1) + self.guard.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("body =") + Doc.nested(4, Doc.break_(1) + self.body.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("IfBranch") + Doc.char('(') + args)


impl ToDoc[FnExpr]:
    toDoc(self: FnExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("sig =") + Doc.nested(4, Doc.break_(1) + self.sig.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("body =") + Doc.nested(4, Doc.break_(1) + self.body.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("idx =") + Doc.nested(4, Doc.break_(1) + self.idx.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("FnExpr") + Doc.char('(') + args)


impl ToDoc[IsExpr]:
    toDoc(self: IsExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("expr =") + Doc.nested(4, Doc.break_(1) + self.expr.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("pat =") + Doc.nested(4, Doc.break_(1) + self.pat.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("IsExpr") + Doc.char('(') + args)


impl ToDoc[DoExpr]:
    toDoc(self: DoExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("body =") + Doc.nested(4, Doc.break_(1) + self.body.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_firstToken =")
                + Doc.nested(4, Doc.break_(1) + self._firstToken.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("DoExpr") + Doc.char('(') + args)


impl ToDoc[UnOp]:
    toDoc(self: UnOp) Doc:
        match self:
            UnOp.Not: Doc.str("UnOp.Not")
            UnOp.Neg: Doc.str("UnOp.Neg")


impl ToDoc[SeqExpr]:
    toDoc(self: SeqExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("elems =")
                + Doc.nested(4, Doc.break_(1) + self.elems.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lbracket =")
                + Doc.nested(4, Doc.break_(1) + self._lbracket.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_rbracket =")
                + Doc.nested(4, Doc.break_(1) + self._rbracket.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("SeqExpr") + Doc.char('(') + args)


impl ToDoc[SeqElem]:
    toDoc(self: SeqElem) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("key =") + Doc.nested(4, Doc.break_(1) + self.key.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("value =")
                + Doc.nested(4, Doc.break_(1) + self.value.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("SeqElem") + Doc.char('(') + args)


impl ToDoc[ParenExpr]:
    toDoc(self: ParenExpr) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("expr =") + Doc.nested(4, Doc.break_(1) + self.expr.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_lparen =")
                + Doc.nested(4, Doc.break_(1) + self._lparen.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_rparen =")
                + Doc.nested(4, Doc.break_(1) + self._rparen.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ParenExpr") + Doc.char('(') + args)
