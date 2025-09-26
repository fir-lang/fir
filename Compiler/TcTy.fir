## A type checking type.
type Ty:
    ## A type constructor, e.g. `Vec`, `Option`, `U32`.
    Con(
        id: TyId,
        kind: Kind,
    )

    ## A unification variable, created by a type scheme when instantiated.
    Var(TyVar)

    ## A type application, e.g. `Vec[U32]`, `Result[E, T]`.
    ##
    ## Because type variables have kind `*`, the constructor can only be a type
    ## constructor.
    ##
    ## Invariant: the `args` vector is not empty.
    App(
        conId: TyId,
        args: Vec[Ty],
        kind: Kind,
    )

    ## Only in type schemes: a quantified type variable.
    ##
    ## Instantiation converts these into unification variables (`Ty.Var`).
    QVar(
        id: Id,
        kind: Kind,
    )

    ## A function type, e.g. `Fn(U32) Str`, `Fn(x: U32, y: U32) T / Err`.
    Fun(
        args: FunArgs,
        ret: Ty,

        ## Exception type of a function is always a `row(variant)`-kinded type
        ## variable. In type schemes, this will be a `QVar`.
        ##
        ## Not available in constructors.
        exn: Option[Ty],
    )

    ## An anonymous record or variant type or row type. E.g. `(a: Str, ..r)`,
    ## `[Err1(Str), ..r]`.
    Anonymous(
        labels: HashMap[Id, Ty],

        ## Row extension. When available, this will be one of:
        ##
        ## - `Ty.Var`: a unification variable.
        ## - `Ty.Con`: a rigid type variable.
        extension: Option[Ty],

        kind: RecordOrVariant,

        ## Whether this is a row type. A row type has its own kind `row`. When
        ## not a row, the type has kind `*`.
        isRow: Bool,
    )


## A unification variable.
##
## Note: `Hash` and `Eq` are implemented based on `id`.
type TyVar(
    ## Identity of the unification variable.
    ##
    ## This is used to compare unification variables for equality.
    id: U32,

    ## Kind of the variable.
    kind: Kind,

    ## Binding level: depth of the scope the unification variable was created
    ## in.
    level: U32,

    ## When unified with a type, this holds the type.
    link: Option[Ty],
)


type FunArgs:
    Positional(Vec[Ty])
    Named(HashMap[Id, Ty])


## Kind of a type.
##
## We don't support higher-kinded variables yet, so this is either a `*` or
## `row` for now.
#[derive(ToDoc)]
type Kind:
    Star
    Row(RecordOrVariant)


#[derive(ToDoc)]
type RecordOrVariant:
    Record
    Variant


# ------------------------------------------------------------------------------


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
