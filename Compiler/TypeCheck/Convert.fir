import [
    Compiler/Ast,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyMap,
]


convertAstTy(tys: TyMap, astTy: Type, loc: Loc) Ty / TypeError:
    match astTy:
        Type.Named(namedTy): convertNamedTy(tys, namedTy, loc)

        # TODO: `id` doesn't have token text.
        Type.Var(var_): panic("TODO")

        Type.Record(_): panic("TODO")

        Type.Variant(_): panic("TODO")

        Type.Fn_(_): panic("TODO")


convertNamedTy(tys: TyMap, namedTy: NamedType, loc: Loc) Ty:
    panic("TODO")
