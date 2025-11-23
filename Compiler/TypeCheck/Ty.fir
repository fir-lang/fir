import [
    Compiler/Defs,
    Compiler/Error,
]


# ------------------------------------------------------------------------------


## A type checking type.
#[derive(ToDoc)]
type Ty:
    ## A type constructor with kind `*`. E.g. `U32`, `Bool`.
    Con(
        id: TyDefIdx,
    )

    ## A type application, e.g. `Vec[U32]`, `Result[E, T]`.
    ##
    ## Invariant: the `args` vector is not empty. Nullary constructor
    ## applications are represented as `Ty.Con`.
    App(
        conId: TyDefIdx,
        args: Vec[Ty],
    )

    # --------------------------------------------------------------------------
    # Variables

    ## A quantified type variable, in type schemes.
    QVar(QVar)

    ## A unification variable, created from a `Ty.QVar` in instantiation.
    UVar(UVar)

    ## A rigid type variable. These are quantified type variables when checking
    ## the body of the function with the quantified type variables.
    RVar(RVar)

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


## Only in type schemes: a quantified type variable.
##
## When instantiated, these become unification variables (`Ty.UVar`).
##
## When checking function bodies, quantified type variables of the function's
## type scheme becomes rigid type variables (`Ty.RVar`).
#[derive(ToDoc)]
type QVar(
    id: LocalId,
    kind: Kind,
)


## A unification variable.
##
## Note: `Hash` and `Eq` are implemented based on `id`.
#[derive(ToDoc)]
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


impl Eq[UVar]:
    __eq(self: UVar, other: UVar) Bool:
        self.id == other.id


UVar.setLink(self, link: Ty):
    assert(self.link is Option.None)
    self.link = Option.Some(link)


## A rigid type variable. These are quantified type variables when checking
## the body of the function with the quantified type variables.
#[derive(ToDoc)]
type RVar(
    id: LocalId,
    kind: Kind,
)


#[derive(ToDoc)]
type FunArgs:
    Positional(Vec[Ty])
    Named(HashMap[LocalId, Ty])


FunArgs.len(self) U32:
    match self:
        FunArgs.Positional(tys): tys.len()
        FunArgs.Named(tys): tys.len()


## Kind of a type.
##
## We don't support higher-kinded variables yet, so this is either a `*` or
## `row` for now.
#[derive(ToDoc)]
type Kind:
    Star
    Row(RecordOrVariant)


impl Eq[Kind]:
    __eq(self: Kind, other: Kind) Bool:
        match (left = self, right = other):
            (left = Kind.Star, right = Kind.Star): Bool.True
            (left = Kind.Row(row1), right = Kind.Row(row2)): row1 == row2
            _: Bool.False


impl Clone[Kind]:
    clone(self: Kind) Kind:
        self


#[derive(ToDoc)]
type RecordOrVariant:
    Record
    Variant


impl Eq[RecordOrVariant]:
    __eq(self: RecordOrVariant, other: RecordOrVariant) Bool:
        match (left = self, right = other):
            (left = RecordOrVariant.Record, right = RecordOrVariant.Record):
                Bool.True
            (left = RecordOrVariant.Variant, right = RecordOrVariant.Variant):
                Bool.True
            _: Bool.False


Ty.kind(self) Kind:
    match self:
        Ty.Con(..) | Ty.App(..) | Ty.Fun(..): Kind.Star

        Ty.QVar(QVar(kind, ..)) | Ty.RVar(RVar(kind, ..)): kind

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


Ty.unitRow(kind: RecordOrVariant) Ty:
    Ty.Anonymous(
        labels = HashMap.empty(),
        extension = Option.None,
        kind,
        isRow = Bool.True,
    )


# ------------------------------------------------------------------------------
# Type schemes and instantiation


#[derive(ToDoc)]
type Scheme(
    ## Generalized (quantified) variables with kinds.
    ##
    ## When the scheme is for a trait method, the first type parameters will be
    ## the type parameters for the trait, in the right order.
    qvars: Vec[QVar],

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


#[derive(ToDoc)]
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
    let varMap = HashMap[LocalId, Ty].withCapacity(self.qvars.len())

    # Instantiated type parameters, in the same order as `self.qvars`.
    let instantiations = Vec[UVar].withCapacity(self.qvars.len())

    # Instantiate qvars of the scheme.
    for qvar: QVar in self.qvars.iter():
        let qvarId = qvar.id
        let qvarKind = qvar.kind

        let uvar = varGen.newVar(level, qvarKind, self.loc)

        let old = varMap.insert(qvarId, Ty.UVar(uvar))
        assert(old is Option.None)

        instantiations.push(uvar)

    # Generate predicates.
    for pred: Pred in self.preds.iter():
        let instantiatedPred = Pred(
            trait_ = pred.trait_,
            params =
                Vec.fromIter(
                    pred.params.iter().map(|param: Ty|: param.substQVars(varMap)),
                ),
            loc,
        )
        preds.push(instantiatedPred)

    (ty = self.ty.substQVars(varMap), vars = instantiations)


Scheme.instantiateWithTys(self, argTys: Vec[Ty], preds: Vec[Pred], loc: Loc,) Ty:
    assert(self.qvars.len() == argTys.len())

    # Maps `QVar`s to unification variables.
    let varMap = HashMap[LocalId, Ty].withCapacity(self.qvars.len())

    for argIdx: U32 in range(u32(0), argTys.len()):
        varMap.insert(self.qvars.get(argIdx).id, argTys.get(argIdx))

    # Generate predicates.
    for pred: Pred in self.preds.iter():
        let instantiatedPred = Pred(
            trait_ = pred.trait_,
            params =
                Vec.fromIter(
                    pred.params.iter().map(|param: Ty|: param.substQVars(varMap)),
                ),
            loc,
        )
        preds.push(instantiatedPred)

    self.ty.substQVars(varMap)


# ------------------------------------------------------------------------------
# Predicates


#[derive(ToDoc)]
type Pred(
    trait_: TyDefIdx,
    params: Vec[Ty],
    loc: Loc,
)


## A set of predicates.
#[derive(ToDoc)]
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
                args =
                    Vec.fromIter(args.iter().map(|ty: Ty|: ty.substQVars(vars))),
            )

        Ty.QVar(QVar(id, ..)):
            vars.get(id).unwrapOrElse(
                ||: panic("Ty.substQVars: unbound QVar `id.name`"),
            )

        Ty.Fun(args, ret, exn):
            Ty.Fun(
                args =
                    match args:
                        FunArgs.Positional(tys):
                            FunArgs.Positional(
                                Vec.fromIter(
                                    tys.iter().map(|ty: Ty|: ty.substQVars(vars)),
                                ),
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
# Generated ToDoc implementations


impl ToDoc[Ty]:
    toDoc(self: Ty) Doc:
        match self:
            Ty.Con(id):
                let args = Doc.break_(0)
                args += Doc.grouped(
                    Doc.str("id =") + Doc.nested(4, Doc.break_(1) + id.toDoc()),
                )
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.str("Ty.Con") + Doc.char('(') + args
            Ty.App(conId, args):
                let args = Doc.break_(0)
                args += Doc.grouped(
                    Doc.str("conId =")
                        + Doc.nested(4, Doc.break_(1) + conId.toDoc()),
                )
                args += Doc.char(',') + Doc.break_(1)
                args += Doc.grouped(
                    Doc.str("args =")
                        + Doc.nested(4, Doc.break_(1) + args.toDoc()),
                )
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.str("Ty.App") + Doc.char('(') + args
            Ty.QVar(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Ty.QVar") + Doc.char('(') + args)
            Ty.UVar(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Ty.UVar") + Doc.char('(') + args)
            Ty.RVar(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("Ty.RVar") + Doc.char('(') + args)
            Ty.Fun(args, ret, exn):
                let args = Doc.break_(0)
                args += Doc.grouped(
                    Doc.str("args =")
                        + Doc.nested(4, Doc.break_(1) + args.toDoc()),
                )
                args += Doc.char(',') + Doc.break_(1)
                args += Doc.grouped(
                    Doc.str("ret =")
                        + Doc.nested(4, Doc.break_(1) + ret.toDoc()),
                )
                args += Doc.char(',') + Doc.break_(1)
                args += Doc.grouped(
                    Doc.str("exn =")
                        + Doc.nested(4, Doc.break_(1) + exn.toDoc()),
                )
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.str("Ty.Fun") + Doc.char('(') + args
            Ty.Anonymous(labels, extension, kind, isRow):
                let args = Doc.break_(0)
                args += Doc.grouped(
                    Doc.str("labels =")
                        + Doc.nested(4, Doc.break_(1) + labels.toDoc()),
                )
                args += Doc.char(',') + Doc.break_(1)
                args += Doc.grouped(
                    Doc.str("extension =")
                        + Doc.nested(4, Doc.break_(1) + extension.toDoc()),
                )
                args += Doc.char(',') + Doc.break_(1)
                args += Doc.grouped(
                    Doc.str("kind =")
                        + Doc.nested(4, Doc.break_(1) + kind.toDoc()),
                )
                args += Doc.char(',') + Doc.break_(1)
                args += Doc.grouped(
                    Doc.str("isRow =")
                        + Doc.nested(4, Doc.break_(1) + isRow.toDoc()),
                )
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.str("Ty.Anonymous") + Doc.char('(') + args


impl ToDoc[QVar]:
    toDoc(self: QVar) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("id =") + Doc.nested(4, Doc.break_(1) + self.id.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("kind =") + Doc.nested(4, Doc.break_(1) + self.kind.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("QVar") + Doc.char('(') + args)


impl ToDoc[UVar]:
    toDoc(self: UVar) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("id =") + Doc.nested(4, Doc.break_(1) + self.id.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("kind =") + Doc.nested(4, Doc.break_(1) + self.kind.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("level =")
                + Doc.nested(4, Doc.break_(1) + self.level.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("link =") + Doc.nested(4, Doc.break_(1) + self.link.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("UVar") + Doc.char('(') + args)


impl ToDoc[RVar]:
    toDoc(self: RVar) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("id =") + Doc.nested(4, Doc.break_(1) + self.id.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("kind =") + Doc.nested(4, Doc.break_(1) + self.kind.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("RVar") + Doc.char('(') + args)


impl ToDoc[FunArgs]:
    toDoc(self: FunArgs) Doc:
        match self:
            FunArgs.Positional(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("FunArgs.Positional") + Doc.char('(') + args)
            FunArgs.Named(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("FunArgs.Named") + Doc.char('(') + args)


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


impl ToDoc[Scheme]:
    toDoc(self: Scheme) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("qvars =")
                + Doc.nested(4, Doc.break_(1) + self.qvars.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("preds =")
                + Doc.nested(4, Doc.break_(1) + self.preds.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("ty =") + Doc.nested(4, Doc.break_(1) + self.ty.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("loc =") + Doc.nested(4, Doc.break_(1) + self.loc.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Scheme") + Doc.char('(') + args)


impl ToDoc[UVarGen]:
    toDoc(self: UVarGen) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_nextId =")
                + Doc.nested(4, Doc.break_(1) + self._nextId.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("UVarGen") + Doc.char('(') + args)


impl ToDoc[Pred]:
    toDoc(self: Pred) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("trait_ =")
                + Doc.nested(4, Doc.break_(1) + self.trait_.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("params =")
                + Doc.nested(4, Doc.break_(1) + self.params.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("loc =") + Doc.nested(4, Doc.break_(1) + self.loc.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Pred") + Doc.char('(') + args)


impl ToDoc[PredSet]:
    toDoc(self: PredSet) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("preds =")
                + Doc.nested(4, Doc.break_(1) + self.preds.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("PredSet") + Doc.char('(') + args)


# ------------------------------------------------------------------------------
# ToStr implementations. These are used when generating error messages, so they
# should be readable by the users and should not expose implementation details.

impl ToStr[Ty]:
    toStr(self: Ty) Str:
        panic("TODO")


impl ToStr[Kind]:
    toStr(self: Kind) Str:
        panic("TODO")
        panic("TODO")


impl ToStr[RecordOrVariant]:
    toStr(self: RecordOrVariant) Str:
        panic("TODO")
