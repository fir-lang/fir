import [
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyCon,
]


type TyMap(
    _vars: ScopeMap[Str, Ty],
)


TyMap.getVar(self, var_: Str) Option[Ty]:
    self._vars.get(var_)


TyMap.insertVar(self, var_: Str, ty: Ty):
    self._vars.insert(var_, ty)
    ()


TyMap.enterVarScope(self):
    self._vars.enterScope()


TyMap.exitVarScope(self) HashMap[Str, Ty]:
    self._vars.exitScope()
