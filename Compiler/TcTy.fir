import [
    Compiler/Defs,
    Compiler/Error,
]


# ------------------------------------------------------------------------------


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
# Type schemes and instantiation


type Scheme(
    ## Generalized variables with kinds.
    ##
    ## When the scheme is for a trait method, the first type parameters will be
    ## the type parameters for the trait, in the right order.
    qvars: Vec[(id: Id, kind: Kind)],

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


type TyVarGen(
    _nextId: U32,
)


TyVarGen.new() TyVarGen:
    TyVarGen(_nextId = 0)


TyVarGen.nextId(self) U32:
    let next = self._nextId
    self._nextId += 1
    next


TyVarGen.newVar(self, level: U32, kind: Kind, loc: Loc) TyVar:
    TyVar(id = self.nextId(), kind, level, link = Option.None,)


## Instantiate the type scheme. Generated predicates are added to `preds`.
## Returns the instantiated type and instantiated type variables of the scheme.
Scheme.instantiate(
    self,
    level: U32,
    varGen: TyVarGen,
    preds: Vec[Pred],
    loc: Loc,
) (ty: Ty, vars: Vec[TyVar]):
    # TODO: We should rename type variables in a renaming pass, or disallow
    # shadowing, or handle shadowing here.

    # Maps `QVar`s to instantiations.
    let varMap: HashMap[Id, Ty] = HashMap.withCapacity(10)

    # Instantiated type parameters, in the same order as `self.qvars`.
    let instantiations: Vec[TyVar] = Vec.withCapacity(self.qvars.len())

    # Instantiate qvars of the scheme.
    for qvarKind: (id: Id, kind: Kind) in self.qvars.iter():
        let qvar = qvarKind.id
        let kind = qvarKind.kind

        let instantiatedVar = varGen.newVar(level, kind, self.loc)

        # TODO: This needs Eq and Hash for Id, but Ids don't have the variable
        # text, and ids from different modules can get mixed. We should be using
        # `Str` or `InternedStr`.
        # let old = varMap.insert(qvar, Ty.Var(instantiatedVar))
        # assert(old is Option.None)
        instantiations.push(instantiatedVar)

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


Ty.substQVars(self, vars: HashMap[Id, Ty]) Ty:
    panic("TODO")


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
