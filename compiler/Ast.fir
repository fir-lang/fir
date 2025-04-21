type Loc:
    file: Str
    byteIdx: U32
    byteLen: U32

type L[a]:
    loc: Loc
    node: a

type Id:
    name: Str
    idx: U32
    loc: Loc

type TopDecl:
    Type(L[TypeDecl])
    Fun(L[FunDecl])
    Import(L[ImportDecl])
    Trait(L[TraitDecl])
    Impl(L[ImplDecl])

type TypeDecl:
    name: Id
    typeParams: Vec[Id]
    typeParamKinds: Vec[Kind]
    rhs: Option[TypeDeclRhs]

type Kind:
    Star
    Row(RecordOrVariant)

type RecordOrVariant:
    Record
    Variant

type TypeDeclRhs:
    Sum(Vec[ConstructorDecl])
    Product(ConstructorFields)

type ConstructorDecl:
    name: Id
    fields: ConstructorFields

type ConstructorFields:
    Empty
    Named(Vec[(name: Id, ty: L[Type])])
    Unnamed(Vec[L[Type]])

type FunDecl:
    parentTy: Option[Id]
    name: Id
    sig: FunSig
    body: Option[Vec[L[Stmt]]]

type FunSig:
    context: Context
    self_: SelfParam
    params: Vec[(name: Id, ty: L[Type])]
    returnTy: Option[L[Type]]
    exceptions: Option[L[Type]]

type SelfParam:
    No
    Implicit
    Explicit(L[Type])

type ImportDecl:
    path: Vec[Str]

type TraitDecl:
    name: Id
    typeParams: Vec[Id]
    typeParamKinds: Vec[Kind]
    items: Vec[FunDecl]

type ImplDecl:
    context: Context
    trait_: Id
    tys: Vec[L[Type]]
    items: Vec[FunDecl]

type Type:
    Named(NamedType)
    Var(Id)
    Record:
        fields: Vec[Named[L[Type]]]
        extension: Option[Id]
    Variant:
        alts: Vec[VariantAlt]
        extension: Option[Id]

type VariantAlt:
    con: Id
    fields: Vec[Named[L[Type]]]

type Context:
    typeParams: Vec[(name: Id, kind: Kind)]
    preds: Vec[L[Type]]

type NamedType:
    name: Id
    args: Vec[L[Type]]

type Named[t]:
    name: Option[Id]
    node: t

# TODO
type Stmt:
    Let(LetStmt)
    Assign(AssignStmt)
    Expr(Expr)
    For(ForStmt)
    While(WhileStmt)
    WhileLet(WhileLetStmt)
    Break:
        label: Option[Id]
        level: U32
    Continue:
        label: Option[Id]
        level: U32

type LetStmt:
    lhs: L[Pat]
    ty: Option[L[Type]]
    rhs: L[Expr]

type AssignStmt:
    lhs: L[Expr]
    rhs: L[Expr]
    op: AssignOp

type AssignOp:
    Eq
    PlusEq
    MinusEq
    StarEq
    CaretEq

type ForStmt:
    label: Option[Id]
    pat: L[Pat]
    astTy: Option[L[Type]]
    tcTy: Option[L[Type]]  # TODO: type-checking type
    expr: L[Expr]
    exprTy: Option[L[Type]] # TODO: type-checking type
    body: Vec[L[Stmt]]

type WhileStmt:
    label: Option[Id]
    cond: L[Expr]
    body: Vec[L[Stmt]]

type WhileLetStmt:
    label: Option[Id]
    pat: L[Pat]
    cond: L[Expr]
    body: Vec[L[Stmt]]

type Pat:
    Var(VarPat)
    Constr(ConstrPat)
    Variant(VariantPat)
    Record(Vec[Named[L[Pat]]])
    Ignore
    Str(Str)
    Char(Char)
    StrPfx(Str, Id)
    Or(L[Pat], L[Pat])

type VarPat:
    var_: Id
    ty: Option[L[Type]]    # TODO: This should be type-checking type instead of AST type

type ConstrPat:
    constr: Constructor
    fields: Vec[Named[L[Pat]]]
    tyArgs: Vec[L[Type]]   # TODO: This should be type-checking type instead of AST type

type VariantPat:
    constr: Id
    fields: Vec[Named[L[Pat]]]

type Constructor:
    type_: Id
    constr: Option[Id]

type Expr:
    Var(VarExpr)
    Constr(ConstrExpr)
    ConstrSelect(ConstrSelectExpr)
    FieldSelect(FieldSelectExpr)
    MethodSelect(MethodSelectExpr)
    AssocFnSelect(AssocFnSelectExpr)
    Call(CallExpr)
    Int(IntExpr)
    Str(Vec[StrPart])
    Char(Char)
    Self
    BinOp(BinOpExpr)
    UnOp(UnOpExpr)
    Record(Vec[Named[L[Expr]]])
    Variant(VariantExpr)
    Return(L[Expr])
    Match(MatchExpr)
    If(IfExpr)
    Fn_(FnExpr)

type VarExpr:
    id: Id
    tyArgs: Vec[L[Type]]

type ConstrExpr:
    id: Id
    tyArgs: Vec[L[Type]]

type ConstrSelectExpr:
    ty: Id
    constr: Id
    tyArgs: Vec[L[Type]]

type FieldSelectExpr:
    object: L[Expr]
    field: Id

type MethodSelectExpr:
    object: L[Expr]
    objectTy: Option[L[Type]]  # TODO: type-checking type
    methodTyId: Id
    method: Id
    tyArgs: Vec[L[Type]]       # TODO: type-checking type

type AssocFnSelectExpr:
    ty: Id
    member: Id
    tyArgs: Vec[L[Type]]       # TODO: type-checking type

type CallExpr:
    fun: L[Expr]
    args: Vec[CallArg]

type CallArg:
    name: Option[Id]
    expr: L[Expr]

type IntExpr:
    text: Str
    suffix: Option[IntKind]
    radix: U32
    parsed: U32

type StrPart:
    Str(Str)
    Expr(L[Expr])

type BinOpExpr:
    left: L[Expr]
    right: L[Expr]
    tyArgs: Vec[L[Type]]       # TODO: type-checking type

type UnOpExpr:
    op: UnOp
    expr: L[Expr]

type VariantExpr:
    id: Id
    args: Vec[Named[L[Expr]]]

type MatchExpr:
    scrutinee: L[Expr]
    alts: Vec[Alt]

type Alt:
    pattern: L[Pat]
    guard: Option[L[Expr]]
    rhs: Vec[L[Stmt]]

type IfExpr:
    branches: Vec[(guard: L[Expr], body: Vec[L[Stmt]])]
    else_branch: Option[Vec[L[Stmt]]]

type FnExpr:
    sig: FunSig
    body: Vec[L[Stmt]]
    idx: U32

type UnOp:
    Not
    Neg
