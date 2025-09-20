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


#[derive(ToDoc)]
type Module(
    ## The module's package.
    _package: PackageUri,

    ## Path of the module in its package.
    _path: Vec[Str],

    _idx: ModuleIdx,

    ## Module-level items that `VarId`s resolve to: top-level variables,
    ## associated functions.
    _varItems: Vec[VarDef],

    ## Module-level items that `TypeId`s resolve to: types, traits.
    _tyItems: Vec[TyDef],
)


# ------------------------------------------------------------------------------
# Function items


#[derive(ToDoc)]
type VarDef:
    Top(TopFunDef)
    Assoc(AssocFunDef)


#[derive(ToDoc)]
type VarDefIdx:
    Local
    Top(TopFunDefIdx)
    Assoc(AssocFunDefIdx)


#[derive(ToDoc)]
type TopFunDef(
    _ast: FunDecl,
    _idx: TopFunDefIdx,
)


#[derive(ToDoc)]
type TopFunDefIdx(
    _mod: ModuleIdx,

    ## Index into the module's `_varItems`.
    _idx: U32,
)


#[derive(ToDoc)]
type AssocFunDef(
    _ast: FunDecl,
    _idx: AssocFunDefIdx,
)


#[derive(ToDoc)]
type AssocFunDefIdx(
    _mod: ModuleIdx,

    ## Index into the module's `_typeItems`.
    ##
    ## Needs to be resolved by the name resolving pass.
    _tyIdx: Option[U32],

    ## Index into the module's `_varItems`.
    _funIdx: U32,
)


# ------------------------------------------------------------------------------
# Type items


#[derive(ToDoc)]
type TyDef(
    _ast: ConDecl,
    _idx: TyDefIdx,
)


#[derive(ToDoc)]
type TyDefIdx(
    _mod: ModuleIdx,

    ## Index into the module's `_tyItems`.
    _tyIdx: U32,
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
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_package =")
                + Doc.nested(4, Doc.break_(1) + self._package.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_path =")
                + Doc.nested(4, Doc.break_(1) + self._path.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_varItems =")
                + Doc.nested(4, Doc.break_(1) + self._varItems.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_tyItems =")
                + Doc.nested(4, Doc.break_(1) + self._tyItems.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Module") + Doc.char('(') + args)


impl ToDoc[VarDef]:
    toDoc(self: VarDef) Doc:
        match self:
            VarDef.Top(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("VarDef.Top") + Doc.char('(') + args)
            VarDef.Assoc(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("VarDef.Assoc") + Doc.char('(') + args)


impl ToDoc[VarDefIdx]:
    toDoc(self: VarDefIdx) Doc:
        match self:
            VarDefIdx.Local: Doc.str("VarDefIdx.Local")
            VarDefIdx.Top(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("VarDefIdx.Top") + Doc.char('(') + args)
            VarDefIdx.Assoc(i0):
                let args = Doc.break_(0)
                args += i0.toDoc()
                args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
                Doc.grouped(Doc.str("VarDefIdx.Assoc") + Doc.char('(') + args)


impl ToDoc[TopFunDef]:
    toDoc(self: TopFunDef) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_ast =") + Doc.nested(4, Doc.break_(1) + self._ast.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TopFunDef") + Doc.char('(') + args)


impl ToDoc[TopFunDefIdx]:
    toDoc(self: TopFunDefIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_mod =") + Doc.nested(4, Doc.break_(1) + self._mod.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TopFunDefIdx") + Doc.char('(') + args)


impl ToDoc[AssocFunDef]:
    toDoc(self: AssocFunDef) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_ast =") + Doc.nested(4, Doc.break_(1) + self._ast.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("AssocFunDef") + Doc.char('(') + args)


impl ToDoc[AssocFunDefIdx]:
    toDoc(self: AssocFunDefIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_mod =") + Doc.nested(4, Doc.break_(1) + self._mod.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_tyIdx =")
                + Doc.nested(4, Doc.break_(1) + self._tyIdx.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_funIdx =")
                + Doc.nested(4, Doc.break_(1) + self._funIdx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("AssocFunDefIdx") + Doc.char('(') + args)


impl ToDoc[TyDef]:
    toDoc(self: TyDef) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_ast =") + Doc.nested(4, Doc.break_(1) + self._ast.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TyDef") + Doc.char('(') + args)


impl ToDoc[TyDefIdx]:
    toDoc(self: TyDefIdx) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_mod =") + Doc.nested(4, Doc.break_(1) + self._mod.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_tyIdx =")
                + Doc.nested(4, Doc.break_(1) + self._tyIdx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TyDefIdx") + Doc.char('(') + args)
