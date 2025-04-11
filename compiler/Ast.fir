type Loc:
    file: Str
    byteIdx: U32
    byteLen: U32

type Id:
    name: Str
    idx: U32
    loc: Loc

type TopDecl:
    Type(TypeDecl)
    Fun(FunDecl)
    Import(ImportDecl)
    Trait(TraitDecl)
    Impl(ImplDecl)

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
    Named(Vec[(name: Id, ty: Type)])
    Unnamed(Vec[Type])

type FunDecl:
    parentTy: Option[Id]
    name: Id
    sig: FunSig
    body: Option[Vec[Stmt]]

type FunSig:
    context: Context
    self_: SelfParam
    params: Vec[(name: Id, ty: Type)]
    returnTy: Option[Type]
    exceptions: Option[Type]

type SelfParam:
    No
    Implicit
    Explicit(Type)

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
    tys: Vec[Type]
    items: Vec[FunDecl]

type Type:
    Named(NamedType)
    Var(Id)
    Record:
        fields: Vec[Named[Type]]
        extension: Option[Id]
    Variant:
        alts: Vec[VariantAlt]
        extension: Option[Id]

type VariantAlt:
    con: Id
    fields: Vec[Named[Type]]

type Context:
    typeParams: Vec[(name: Id, kind: Kind)]
    preds: Vec[Type]

type NamedType:
    name: Id
    args: Vec[Type]

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
    lhs: Pat
    ty: Option[Type]
    rhs: Expr

type AssignStmt:
    lhs: Expr
    rhs: Expr
    op: AssignOp

type AssignOp:
    Eq
    PlusEq
    MinusEq
    StarEq
    CaretEq

type ForStmt:
    label: Option[Id]
    pat: Pat
    astTy: Option[Type]
    tcTy: Option[Type]  # TODO: type-checking type
    expr: Expr
    exprTy: Option[Type] # TODO: type-checking type
    body: Vec[Stmt]

type WhileStmt:
    label: Option[Id]
    cond: Expr
    body: Vec[Stmt]

type WhileLetStmt:
    label: Option[Id]
    pat: Pat
    cond: Expr
    body: Vec[Stmt]

type Pat:
    Var(VarPat)
    Constr(ConstrPat)
    Variant(VariantPat)
    Record(Vec[Named[Pat]])
    Ignore
    Str(Str)
    Char(Char)
    StrPfx(Str, Id)
    Or(Pat, Pat)

type VarPat:
    var_: Id
    ty: Option[Type]    # TODO: This should be type-checking type instead of AST type

type ConstrPat:
    constr: Constructor
    fields: Vec[Named[Pat]]
    tyArgs: Vec[Type]   # TODO: This should be type-checking type instead of AST type

type VariantPat:
    constr: Id
    fields: Vec[Named[Pat]]

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
    Record(Vec[Named[Expr]])
    Variant(VariantExpr)
    Return(Expr)
    Match(MatchExpr)
    If(IfExpr)
    Fn_(FnExpr)

type VarExpr:
    id: Id
    tyArgs: Vec[Type]

type ConstrExpr:
    id: Id
    tyArgs: Vec[Type]

type ConstrSelectExpr:
    ty: Id
    constr: Id
    tyArgs: Vec[Type]

type FieldSelectExpr:
    object: Expr
    field: Id

type MethodSelectExpr:
    object: Expr
    objectTy: Option[Type]  # TODO: type-checking type
    methodTyId: Id
    method: Id
    tyArgs: Vec[Type]       # TODO: type-checking type

type AssocFnSelectExpr:
    ty: Id
    member: Id
    tyArgs: Vec[Type]       # TODO: type-checking type

type CallExpr:
    fun: Expr
    args: Vec[CallArg]

type CallArg:
    name: Option[Id]
    expr: Expr

type IntExpr:
    text: Str
    suffix: Option[IntKind]
    radix: U32
    parsed: U32

type StrPart:
    Str(Str)
    Expr(Expr)

type BinOpExpr:
    left: Expr
    right: Expr
    tyArgs: Vec[Type]       # TODO: type-checking type

type UnOpExpr:
    op: UnOp
    expr: Expr

type VariantExpr:
    id: Id
    args: Vec[Named[Expr]]

type MatchExpr:
    scrutinee: Expr
    alts: Vec[Alt]

type Alt:
    pattern: Pat
    guard: Option[Expr]
    rhs: Vec[Stmt]

type IfExpr:
    branches: Vec[(guard: Expr, body: Vec[Stmt])]
    else_branch: Option[Vec[Stmt]]

type FnExpr:
    sig: FunSig
    body: Vec[Stmt]
    idx: U32

type UnOp:
    Not
    Neg
