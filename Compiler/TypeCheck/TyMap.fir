import [
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyCon,
]


type TyMap(
    cons: HashMap[Str, TyCon],
    vars: HashMap[Str, Ty],
)
