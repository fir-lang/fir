## Defines identifiers, packages, modules, module-level items.


import [Compiler/Ast]


# ------------------------------------------------------------------------------
# Identifiers


## A term variable id.
##
## This can refer to: local variables, top-level variables, associated
## functions, trait methods.
type VarId(
    _token: TokenIdx,
    _resolved: Option[VarDefIdx],
)


## A type id.
##
## These can refer to: product and sum types, traits.
type TyId(
    _token: TokenIdx,
    _resolved: Option[TyDefIdx],
)


# ------------------------------------------------------------------------------
# Packages and modules


type PackageUri(
    _uri: Str,
)


type ModuleIdx(
    ## Index of the module in the program.
    _idx: U32,
)


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


type VarDef:
    Top(TopFunDef)
    Assoc(AssocFunDef)


type VarDefIdx:
    Local
    Top(TopFunDefIdx)
    Assoc(AssocFunDefIdx)


type TopFunDef(
    _ast: FunDecl,
    _idx: TopFunDefIdx,
)


type TopFunDefIdx(
    _mod: ModuleIdx,

    ## Index into the module's `_varItems`.
    _idx: U32,
)


type AssocFunDef(
    _ast: FunDecl,
    _idx: AssocFunDefIdx,
)


type AssocFunDefIdx(
    _mod: ModuleIdx,

    ## Index into the module's `_typeItems`.
    _tyIdx: U32,

    ## Index into the module's `_varItems`.
    _funIdx: U32,
)


# ------------------------------------------------------------------------------
# Type items


type TyDef(
    _ast: ConDecl,
    _idx: TyDefIdx,
)


type TyDefIdx(
    _mod: ModuleIdx,

    ## Index into the module's `_tyItems`.
    _tyIdx: U32,
)
