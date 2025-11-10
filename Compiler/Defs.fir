## Defines identifiers, packages, modules, module-level items.


import [
    Compiler/Ast,
    Compiler/Module,
    Compiler/TypeCheck/TyCon,
]


# ------------------------------------------------------------------------------
# Identifiers


## Local ids refer to function and type -local things, they cannot refer to
## top-level things.
##
## This type is used both in binder position (e.g. function arguments, patterns,
## type arguments) and use position (e.g. expressions, type variables).
#[derive(ToDoc)]
type LocalId(
    name: Str,
)


impl Eq[LocalId]:
    __eq(self: LocalId, other: LocalId) Bool:
        self.name == other.name


impl Hash[LocalId]:
    hash(self: LocalId) U32:
        self.name.hash()


## A term variable id.
##
## This can refer to: local variables, top-level variables, associated
## functions.
#[derive(ToDoc)]
type VarId(
    ## Index of the identifier's token in its module.
    token: TokenIdx,

    ## Text of the token at `token`.
    name: Str,

    _resolved: Option[VarDefIdx],
)


VarId.resolve(self, def: VarDefIdx):
    assert(self._resolved is Option.None)
    self._resolved = Option.Some(def)


#[derive(ToDoc)]
type AssocVarId(
    ## Index of the associated member identifier's token in its module.
    token: TokenIdx,

    ## Text of the token at `token`.
    name: Str,

    _resolved: Option[AssocVarDefIdx],
)


## A type id.
##
## These can refer to: product and sum types, traits.
#[derive(ToDoc)]
type TyId(
    ## Index of the type identifier's token in its module.
    token: TokenIdx,

    ## Text of the token at `token`.
    name: Str,

    _resolved: Option[TyDefIdx],
)


TyId.resolve(self, def: TyDefIdx):
    assert(self._resolved is Option.None)
    self._resolved = Option.Some(def)


TyId.def(self) TyDefIdx:
    self._resolved.unwrapOrElse(||: panic("Type id is not resolved yet"))


# ------------------------------------------------------------------------------
# Function items


#[derive(ToDoc)]
type VarDefIdx:
    Local
    Top(TopVarDefIdx)


impl Eq[VarDefIdx]:
    __eq(self: VarDefIdx, other: VarDefIdx) Bool:
        match (left = self, right = other):
            (left = VarDefIdx.Local, right = VarDefIdx.Local): Bool.True
            (left = VarDefIdx.Top(l1), right = VarDefIdx.Top(r1)): l1 == r1
            _: Bool.False


#[derive(ToDoc)]
type TopVarDefIdx(
    ## Module of the variable.
    _mod: ModuleIdx,

    ## Name of the variable in the module.
    ##
    ## This name can be different than the use site name.
    _name: Str,
)


impl Eq[TopVarDefIdx]:
    __eq(self: TopVarDefIdx, other: TopVarDefIdx) Bool:
        self._mod == other._mod and self._name == other._name


#[derive(ToDoc)]
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


impl Eq[AssocVarDefIdx]:
    __eq(self: AssocVarDefIdx, other: AssocVarDefIdx) Bool:
        self._mod == other._mod
            and self._tyName == other._tyName
            and self._varName == other._varName


# ------------------------------------------------------------------------------
# Type items


#[derive(ToDoc)]
type TyDefIdx(
    ## The type's module.
    _mod: ModuleIdx,

    ## Name of the type in `_mod`.
    _name: Str,

    ## Kind of the definition: type or trait.
    _kind: TyDefKind,
)


#[derive(ToDoc)]
type TyDefKind:
    Type
    Trait


impl Eq[TyDefIdx]:
    __eq(self: TyDefIdx, other: TyDefIdx) Bool:
        self._mod == other._mod
            and self._name == other._name
            and self._kind == other._kind


impl Eq[TyDefKind]:
    __eq(self: TyDefKind, other: TyDefKind) Bool:
        match self:
            TyDefKind.Type: other is TyDefKind.Type
            TyDefKind.Trait: other is TyDefKind.Trait


# ------------------------------------------------------------------------------
# Generated ToDoc implementations


impl ToDoc[LocalId]:
    toDoc(self: LocalId) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("name =") + Doc.nested(4, Doc.break_(1) + self.name.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("LocalId") + Doc.char('(') + args)


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


impl ToDoc[VarDefIdx]:
    toDoc(self: VarDefIdx) Doc:
        match self:
            VarDefIdx.Local: Doc.str("VarDefIdx.Local")
            VarDefIdx.Top(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("VarDefIdx.Top") + Doc.char('(') + args)


impl ToDoc[TopVarDefIdx]:
    toDoc(self: TopVarDefIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_mod =") + Doc.nested(4, Doc.break_(1) + self._mod.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_name =")
                + Doc.nested(4, Doc.break_(1) + self._name.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TopVarDefIdx") + Doc.char('(') + args)


impl ToDoc[AssocVarDefIdx]:
    toDoc(self: AssocVarDefIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_mod =") + Doc.nested(4, Doc.break_(1) + self._mod.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_tyName =")
                + Doc.nested(4, Doc.break_(1) + self._tyName.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_varName =")
                + Doc.nested(4, Doc.break_(1) + self._varName.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("AssocVarDefIdx") + Doc.char('(') + args)


impl ToDoc[TyDefIdx]:
    toDoc(self: TyDefIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_mod =") + Doc.nested(4, Doc.break_(1) + self._mod.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_name =")
                + Doc.nested(4, Doc.break_(1) + self._name.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_kind =")
                + Doc.nested(4, Doc.break_(1) + self._kind.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TyDefIdx") + Doc.char('(') + args)


impl ToDoc[TyDefKind]:
    toDoc(self: TyDefKind) Doc:
        match self:
            TyDefKind.Type: Doc.str("TyDefKind.Type")
            TyDefKind.Trait: Doc.str("TyDefKind.Trait")


# ------------------------------------------------------------------------------
# ToStr implementations. These are used when generating error messages, so they
# should be readable by the users and should not expose implementation details.

impl ToStr[LocalId]:
    toStr(self: LocalId) Str:
        panic("TODO")
