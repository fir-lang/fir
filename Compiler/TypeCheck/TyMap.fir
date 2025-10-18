import [
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyCon,
]


type TyMap(
    cons: HashMap[Str, TyCon],
    vars: HashMap[Str, Ty],
)


TyMap.getVar(self, var_: Str) Option[Ty]:
    self.vars.get(var_)


TyMap.getCon(self, con: Str) Option[TyCon]:
    self.cons.get(con)
