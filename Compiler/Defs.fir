## Defines identifiers, packages, modules, module-level items.


import [
    Compiler/Ast,
    Compiler/Module,
]


# ------------------------------------------------------------------------------
# Identifiers


## Local ids refer to function and type -local things, they cannot refer to
## top-level things.
##
## This type is used both in binder position (e.g. function arguments, patterns,
## type arguments) and use position (e.g. expressions, type variables).
#[derive(ToDoc, Eq)]
value type LocalId(
    name: Str,
)


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


VarId.def(self) VarDefIdx:
    self._resolved.unwrapOrElse(
        \(): panic("Term id (\``self.name`\`) is not resolved yet"),
    )


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
    self._resolved.unwrapOrElse(
        \(): panic("Type id (\``self.name`\`) is not resolved yet"),
    )


# ------------------------------------------------------------------------------
# Function items


#[derive(ToDoc, Eq)]
value type VarDefIdx:
    Local
    Top(TopVarDefIdx)


#[derive(ToDoc, Eq)]
value type TopVarDefIdx(
    ## Module of the variable.
    _mod: ModuleIdx,

    ## Name of the variable in the module.
    ##
    ## This name can be different than the use site name.
    _name: Str,
)


#[derive(ToDoc, Eq)]
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


#[derive(ToDoc, Eq)]
value type TyDefIdx(
    ## The type's module.
    _mod: ModuleIdx,

    ## Name of the type in `_mod`.
    _name: Str,
)


impl Hash[TyDefIdx]:
    hash(self: TyDefIdx) U32:
        self._mod.hash() + self._name.hash()


# ------------------------------------------------------------------------------
# ToStr implementations. These are used when generating error messages, so they
# should be readable by the users and should not expose implementation details.


impl ToStr[LocalId]:
    toStr(self: LocalId) Str:
        panic("TODO")
