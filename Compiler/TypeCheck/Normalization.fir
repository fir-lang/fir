import [Compiler/TypeCheck/Ty]


Ty.normalize(self) Ty:
    match self:
        Ty.UVar(uvar): uvar.normalize()
        _: self


UVar.normalize(self) Ty:
    match self.link:
        Option.None: Ty.UVar(self)
        Option.Some(link):
            let linkNormal = link.normalize()
            self.link = Option.Some(linkNormal)
            linkNormal
