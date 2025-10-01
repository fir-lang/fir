import [Compiler/TypeCheck/Ty]


type UnificationError


unify(ty1: Ty, ty2: Ty, varGen: UVarGen, level: U32, loc: Loc) / UnificationError:
    panic("TODO")


unifyOneWay(ty1: Ty, ty2: Ty, varGen: UVarGen, level: U32, loc: Loc) / UnificationError:
    panic("TODO")
