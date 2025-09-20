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

    ## Imported modules. These are used when resolving identifiers.
    _imports: Vec[ModuleIdx],

    _tokens: Array[Token],
)


# ------------------------------------------------------------------------------
# Function items


#[derive(ToDoc)]
type VarDef(
    _ast: FunDecl,
    _idx: TopVarDefIdx,
)


#[derive(ToDoc)]
type VarDefIdx:
    Local
    Top(TopVarDefIdx)

#[derive(ToDoc)]
type TopVarDefIdx (
    _mod: ModuleIdx,

    ## Index into the module's `_varItems`.
    _idx: U32,
)


# ------------------------------------------------------------------------------
# Type items


#[derive(ToDoc)]
type TyDef(
    _ast: TypeDecl,
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
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_imports =")
                + Doc.nested(4, Doc.break_(1) + self._imports.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_tokens =")
                + Doc.nested(4, Doc.break_(1) + self._tokens.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("Module") + Doc.char('(') + args)


impl ToDoc[VarDef]:
    toDoc(self: VarDef) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_ast =") + Doc.nested(4, Doc.break_(1) + self._ast.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("VarDef") + Doc.char('(') + args)


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
            Doc.str("_idx =") + Doc.nested(4, Doc.break_(1) + self._idx.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TopVarDefIdx") + Doc.char('(') + args)


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

