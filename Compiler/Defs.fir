## Defines identifiers, packages, modules, module-level items.


import [Compiler/Ast]


# ------------------------------------------------------------------------------
# Identifiers


## A term variable id.
##
## This can refer to: local variables, top-level variables, associated
## functions.
#[derive(ToDoc)]
type VarId(
    token: TokenIdx,
    _resolved: Option[VarDefIdx],
)


VarId.new(token: TokenIdx) VarId:
    VarId(token, _resolved = Option.None)


#[derive(ToDoc)]
type AssocVarId(
    token: TokenIdx,
    _resolved: Option[AssocVarDefIdx],
)


## A type id.
##
## These can refer to: product and sum types, traits.
#[derive(ToDoc)]
type TyId(
    token: TokenIdx,
    _resolved: Option[TyDefIdx],
)


TyId.new(token: TokenIdx) TyId:
    TyId(token, _resolved = Option.None)


# ------------------------------------------------------------------------------
# Packages and modules


#[derive(ToDoc)]
type PackageUri(
    _uri: Str,
)


#[derive(ToDoc)]
type ModuleIdx(
    ## Index of the module in the program.
    _idx: U32,
)


impl Eq[ModuleIdx]:
    __eq(self: ModuleIdx, other: ModuleIdx) Bool:
        self._idx == other._idx


impl Hash[ModuleIdx]:
    hash(self: ModuleIdx) U32:
        self._idx


#[derive(ToDoc)]
type Module(
    ## The module's package.
    _package: PackageUri,

    ## Path of the module in its package.
    _path: Vec[Str],

    _idx: ModuleIdx,

    ## Functions defined in the module.
    _funItems: HashMap[Str, FunDecl],

    ## Associated functions (including methods, but not trait methods) defined
    ## in the module.
    _assocItems: HashMap[Str, HashMap[Str, FunDecl]],

    ## Types defined in the module.
    _tyItems: HashMap[Str, TypeDecl],

    ## Traits defined in the module.
    _traitItems: HashMap[Str, TraitDecl],

    ## Impls defined in the module.
    _impls: Vec[ImplDecl],

    ## Imported modules. These are used when resolving identifiers.
    _imports: Vec[ModuleIdx],

    ## Tokens of the module. ASTs in the other fields for definitions in the
    ## current module refer to tokens in this array.
    _tokens: Array[Token],

    # Term environment of the module, used for name resolving.
    _termEnv: HashMap[Str, VarDefIdx],

    # Associated item environment of the module, used for name resolving.
    _assocTermEnv: HashMap[Str, HashMap[Str, AssocVarDefIdx]],

    # Type environment of the module, used for name resolving.
    _tyEnv: HashMap[Str, TyDefIdx],

    # Strongly connected component index of the module in the program. Generated
    # by the dependency analysis.
    _sccIdx: Option[U32],
)


# ------------------------------------------------------------------------------
# Function items


#[derive(ToDoc)]
type VarDefIdx:
    Local
    Top(TopVarDefIdx)


#[derive(ToDoc)]
type TopVarDefIdx(
    ## Module of the variable.
    _mod: ModuleIdx,

    ## Name of the variable in the module.
    ##
    ## This name can be different than the use site name.
    _name: Str,
)


type AssocVarDefIdx(
    ## Module of the type.
    ##
    ## Note: both the type and the associated function definition need to be in
    ## the same module, which should also be the type's module. (mainly to keep
    ## things simple)
    _mod: ModuleIdx,

    ## Name of the associated function's type in `_tyModule`.
    _tyName: Str,

    ## Name of the associated function in `_varModule`.
    _varName: Str,
)


# ------------------------------------------------------------------------------
# Type items


#[derive(ToDoc)]
type TyDefIdx:
    Trait(TraitDefIdx)
    Type(TyDefIdx_)


#[derive(ToDoc)]
type TraitDefIdx(
    ## The trait's module.
    _mod: ModuleIdx,

    ## Name of the trait in `_mod`.
    _name: Str,
)


#[derive(ToDoc)]
type TyDefIdx_(
    ## The type's module.
    _mod: ModuleIdx,

    ## Name of the type in `_mod`.
    _name: Str,
)


# ------------------------------------------------------------------------------


impl ToDoc[VarId]:
    toDoc(self: VarId) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("token =")
                + Doc.nested(4, Doc.break_(1) + self.token.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_resolved =")
                + Doc.nested(4, Doc.break_(1) + self._resolved.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("VarId") + Doc.char('(') + args)


impl ToDoc[AssocVarId]:
    toDoc(self: AssocVarId) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("token =")
                + Doc.nested(4, Doc.break_(1) + self.token.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_resolved =")
                + Doc.nested(4, Doc.break_(1) + self._resolved.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("AssocVarId") + Doc.char('(') + args)


impl ToDoc[TyId]:
    toDoc(self: TyId) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("token =")
                + Doc.nested(4, Doc.break_(1) + self.token.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_resolved =")
                + Doc.nested(4, Doc.break_(1) + self._resolved.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TyId") + Doc.char('(') + args)


impl ToDoc[PackageUri]:
    toDoc(self: PackageUri) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_uri =") + Doc.nested(4, Doc.break_(1) + self._uri.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("PackageUri") + Doc.char('(') + args)


impl ToDoc[ModuleIdx]:
    toDoc(self: ModuleIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ModuleIdx") + Doc.char('(') + args)


impl ToDoc[Module]:
    toDoc(self: Module) Doc:
        panic("TODO")


impl ToDoc[VarDefIdx]:
    toDoc(self: VarDefIdx) Doc:
        match self:
            VarDefIdx.Local: Doc.str("VarDefIdx.Local")
            VarDefIdx.Top(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("VarDefIdx.Top") + Doc.char('(') + args)


impl ToDoc[AssocVarDefIdx]:
    toDoc(self: AssocVarDefIdx) Doc:
        panic("TODO")


impl ToDoc[TopVarDefIdx]:
    toDoc(self: TopVarDefIdx) Doc:
        panic("TODO")


impl ToDoc[TyDefIdx]:
    toDoc(self: TyDefIdx) Doc:
        match self:
            TyDefIdx.Trait(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TyDefIdx.Trait") + Doc.char('(') + args)
            TyDefIdx.Type(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("TyDefIdx.Type") + Doc.char('(') + args)


impl ToDoc[TraitDefIdx]:
    toDoc(self: TraitDefIdx) Doc:
        panic("TODO")


impl ToDoc[TyDefIdx_]:
    toDoc(self: TyDefIdx_) Doc:
        panic("TODO")
