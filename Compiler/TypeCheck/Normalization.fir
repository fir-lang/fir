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


Ty.deepNormalize(self) Ty:
    match self:
        Ty.Con(..): self

        Ty.App(conId, args):
            Ty.App(
                conId,
                args =
                    Vec.fromIter(
                        args.iter().map(\(arg: Ty): arg.deepNormalize()),
                    ),
            )

        Ty.QVar(_): panic("QVar in deepNormalize")

        Ty.UVar(uvar):
            if uvar.link is Option.None:
                return self

            let uvarLink = uvar.normalize().deepNormalize()
            uvar.link = Option.Some(uvarLink)
            uvarLink

        Ty.RVar(_): self

        Ty.Fun(args, ret, exn):
            Ty.Fun(
                args =
                    match args:
                        FunArgs.Positional(tys):
                            FunArgs.Positional(
                                Vec.fromIter(
                                    tys.iter().map(\(ty: Ty): ty.deepNormalize()),
                                ),
                            )
                        FunArgs.Named(tys):
                            FunArgs.Named(
                                HashMap.fromIter(
                                    tys.iter().map(
                                        \(ty: HashMapEntry[LocalId, Ty]):
                                            (
                                                key = ty.key,
                                                value = ty.value.deepNormalize(),
                                            ),
                                    ),
                                ),
                            ),
                ret = ret.deepNormalize(),
                exn = exn.map(\(ty: Ty): ty.deepNormalize()),
            )

        Ty.Anonymous(labels, extension, kind, isRow):
            Ty.Anonymous(
                labels =
                    HashMap.fromIter(
                        labels.iter().map(
                            \(label: HashMapEntry[LocalId, Ty]):
                                (
                                    key = label.key,
                                    value = label.value.deepNormalize(),
                                ),
                        ),
                    ),
                extension = extension.map(\(ty: Ty): ty.deepNormalize()),
                kind,
                isRow,
            )
