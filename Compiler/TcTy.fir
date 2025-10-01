import [
    Compiler/Defs,
    Compiler/Error,
]


# ------------------------------------------------------------------------------


## A type checking type.
type Ty:
    ## A type constructor with kind `*`. E.g. `U32`, `Bool`.
    Con(
        id: TyId,
    )

    ## A type application, e.g. `Vec[U32]`, `Result[E, T]`.
    ##
    ## Invariant: the `args` vector is not empty. Nullary constructor
    ## applications are represented as `Ty.Con`.
    App(
        conId: TyId,
        args: Vec[Ty],
    )

    # --------------------------------------------------------------------------
    # Variables

    ## Only in type schemes: a quantified type variable.
    ##
    ## When instantiated, these become unification variables (`Ty.UVar`).
    ##
    ## When checking function bodies, quantified type variables of the
    ## function's type scheme becomes rigid type variables (`Ty.RVar`).
    QVar(
        id: LocalId,
        kind: Kind,
    )

    ## A unification variable, created from a `Ty.QVar` in instantiation.
    UVar(UVar)

    ## A rigid type variable. These are quantified type variables when checking
    ## the body of the function with the quantified type variables.
    RVar(
        id: LocalId,
        kind: Kind,
    )

    # --------------------------------------------------------------------------

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
        labels: HashMap[LocalId, Ty],

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
type UVar(
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
    Named(HashMap[LocalId, Ty])


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


Ty.kind(self) Kind:
    match self:
        Ty.Con(..) | Ty.App(..) | Ty.Fun(..): Kind.Star

        Ty.QVar(kind, ..) | Ty.RVar(kind, ..): kind

        Ty.UVar(uvar): uvar.kind

        Ty.Anonymous(kind, ..): Kind.Row(kind)


Ty.unit() Ty:
    Ty.Anonymous(
        labels = HashMap.empty(),
        extension = Option.None,
        kind = RecordOrVariant.Record,
        isRow = Bool.False,
    )


Ty.emptyVariant() Ty:
    Ty.Anonymous(
        labels = HashMap.empty(),
        extension = Option.None,
        kind = RecordOrVariant.Variant,
        isRow = Bool.False,
    )


# ------------------------------------------------------------------------------
# Type schemes and instantiation


type Scheme(
    ## Generalized (quantified) variables with kinds.
    ##
    ## When the scheme is for a trait method, the first type parameters will be
    ## the type parameters for the trait, in the right order.
    qvars: Vec[(id: LocalId, kind: Kind)],

    ## Predicates of the type scheme. These can refer to `qvars` and need to be
    ## instantiated with `qvars`.
    ##
    ## This is a `Vec`, so in principle it can contain duplicates. Schemes are
    ## currently only generated from top-level functions, which have explicit
    ## type signatures. So the only way to have duplicates here is when the user
    ## writes duplicate predicates.
    ##
    ## Duplicates in predicates are harmless, just cause extra work when
    ## resolving the predicates at the call sites.
    preds: Vec[Pred],

    ## The generalized type.
    # TODO: Should we have separate fields for arguments types and return type?
    ty: Ty,

    ## Location of the scheme's function (or field etc.).
    loc: Loc,
)


type UVarGen(
    _nextId: U32,
)


UVarGen.new() UVarGen:
    UVarGen(_nextId = 0)


UVarGen.nextId(self) U32:
    let next = self._nextId
    self._nextId += 1
    next


UVarGen.newVar(self, level: U32, kind: Kind, loc: Loc) UVar:
    UVar(id = self.nextId(), kind, level, link = Option.None)


## Instantiate the type scheme. Generated predicates are added to `preds`.
## Returns the instantiated type and instantiated type variables of the scheme.
Scheme.instantiate(
    self,
    level: U32,
    varGen: UVarGen,
    preds: Vec[Pred],
    loc: Loc,
) (ty: Ty, vars: Vec[UVar]):
    # TODO: We should rename type variables in a renaming pass, or disallow
    # shadowing, or handle shadowing here.

    # Maps `QVar`s to unification variables.
    let varMap = HashMap[LocalId, Ty].withCapacity(10)

    # Instantiated type parameters, in the same order as `self.qvars`.
    let instantiations = Vec[UVar].withCapacity(self.qvars.len())

    # Instantiate qvars of the scheme.
    for qvarKind: (id: LocalId, kind: Kind) in self.qvars.iter():
        let qvar = qvarKind.id
        let kind = qvarKind.kind

        let uvar = varGen.newVar(level, kind, self.loc)

        let old = varMap.insert(qvar, Ty.UVar(uvar))
        assert(old is Option.None)

        instantiations.push(uvar)

    # Generate predicates.
    for pred: Pred in self.preds.iter():
        let instantiatedPred = Pred(
            trait_ = pred.trait_,
            params =
                pred.params.iter().map(|param: Ty|: param.substQVars(varMap))
                    .toVec(),
            loc,
        )
        preds.push(instantiatedPred)

    (ty = self.ty.substQVars(varMap), vars = instantiations)


# ------------------------------------------------------------------------------
# Predicates


type Pred(
    trait_: TyId,
    params: Vec[Ty],
    loc: Loc,
)


## A set of predicates.
type PredSet(
    ## The set is actually a `Vec`, at least for now.
    ##
    ## The reason why we don't use a `HashSet` here is because the type checker
    ## never adds a duplicate predicates, because it visits every expression
    ## just once, and predicates hold source code location of the expression
    ## that created them. So even if we have e.g. `Eq[U32]` multiple times here,
    ## each of those predicates will have a different location.
    ##
    ## The only way to have duplicate predicates is when a user has a signature
    ## with the same predicate multiple times. In that case `Scheme.preds` will
    ## have duplicates, and calling the function will create duplicate
    ## predicates. Those are harmless, just cause more work when resolving them.
    preds: Vec[Pred],
)


# ------------------------------------------------------------------------------
# Substitutions


Ty.substQVars(self, vars: HashMap[LocalId, Ty]) Ty:
    match self:
        Ty.Con(..) | Ty.UVar(..) | Ty.RVar(..): self

        Ty.App(conId, args):
            Ty.App(
                conId,
                args = args.iter().map(|ty: Ty|: ty.substQVars(vars)).toVec(),
            )

        Ty.QVar(id, ..):
            vars.get(id).unwrapOrElse(
                ||: panic("Ty.substQVars: unbound QVar `id.name`"),
            )

        Ty.Fun(args, ret, exn):
            Ty.Fun(
                args =
                    match args:
                        FunArgs.Positional(tys):
                            FunArgs.Positional(
                                tys.iter().map(|ty: Ty|: ty.substQVars(vars))
                                    .toVec(),
                            )
                        FunArgs.Named(tys):
                            FunArgs.Named(
                                HashMap.fromIter(
                                    tys.iter().map(
                                        |entry: HashMapEntry[LocalId, Ty]|:
                                            (
                                                key = entry.key,
                                                value =
                                                    entry.value.substQVars(vars),
                                            ),
                                    ),
                                ),
                            ),
                ret = ret.substQVars(vars),
                exn = exn.map(|exn: Ty|: exn.substQVars(vars)),
            )

        Ty.Anonymous(labels, extension, kind, isRow):
            Ty.Anonymous(
                labels =
                    HashMap.fromIter(
                        labels.iter().map(
                            |entry: HashMapEntry[LocalId, Ty]|:
                                (
                                    key = entry.key,
                                    value = entry.value.substQVars(vars),
                                ),
                        ),
                    ),
                extension = extension.map(|ty: Ty|: ty.substQVars(vars)),
                kind,
                isRow,
            )


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
