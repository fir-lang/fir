import [
    Compiler/TypeCheck/Normalization,
    Compiler/TypeCheck/RowUtils,
    Compiler/TypeCheck/Ty,
]


type UnificationError


unify(ty1: Ty, ty2: Ty, varGen: UVarGen, level: U32, loc: Loc) / UnificationError:
    ty1 = ty1.normalize()
    ty2 = ty2.normalize()

    match (ty1 = ty1, ty2 = ty2):
        (ty1 = Ty.Con(id = id1), ty2 = Ty.Con(id = id2)):
            if id1.def() != id2.def():
                throw(UnificationError)

        (
            ty1 = Ty.App(conId = id1, args = args1),
            ty2 = Ty.App(conId = id2, args = args2),
        ):
            if id1.def() != id2.def():
                throw(UnificationError)

            if args1.len() != args2.len():
                panic(
                    "`loc`: BUG: Kind error: type constructor TODO applied to different number of arguments in unify",
                )

            for argIdx: U32 in range(u32(0), args1.len()):
                unify(args1.get(argIdx), args2.get(argIdx), varGen, level, loc)

        (ty1 = Ty.QVar(_), ..) | (ty2 = Ty.QVar(_), ..):
            panic("`loc`: BUG: QVar in unification")

        (ty1 = Ty.UVar(var1), ty2 = Ty.UVar(var2)):
            if var1.id == var2.id:
                return

            # We've normalized the types, so the links must be followed to the
            # end.
            assert(var1.link is Option.None)
            assert(var2.link is Option.None)

            if var1.level < var2.level:
                linkVar(var1, ty2)
            else:
                linkVar(var2, ty1)

        (ty1 = Ty.UVar(var1), ty2 = ty2):
            if var1.kind != ty2.kind():
                throw(UnificationError)

            linkVar(var1, ty2)

        (ty1 = ty1, ty2 = Ty.UVar(var2)):
            if var2.kind != ty1.kind():
                throw(UnificationError)

            linkVar(var2, ty1)

        (
            ty1 = Ty.Fun(args = args1, ret = ret1, exn = exn1),
            ty2 = Ty.Fun(args = args2, ret = ret2, exn = exn2),
        ):
            match (args1 = args1, args2 = args2):
                (
                    args1 = FunArgs.Positional(args1),
                    args2 = FunArgs.Positional(args2),
                ):
                    if args1.len() != args2.len():
                        throw(UnificationError)

                    for argIdx: U32 in range(u32(0), args1.len()):
                        unify(
                            args1.get(argIdx),
                            args2.get(argIdx),
                            varGen,
                            level,
                            loc,
                        )

                (args1 = FunArgs.Named(args1), args2 = FunArgs.Named(args2)):
                    # TODO: HashMap.len and HashSet.len
                    # if args1.len() != args2.len():
                    #     throw(UnificationError)

                    for arg1: HashMapEntry[LocalId, Ty] in args1.iter():
                        let arg2 = args2.get(arg1.key).unwrapOrElse(
                            ||: throw(UnificationError),
                        )
                        unify(arg1.value, arg2, varGen, level, loc)

                _: throw(UnificationError)

            match (exn1 = exn1, exn2 = exn2):
                (exn1 = Option.Some(exn1), exn2 = Option.Some(exn2)):
                    unify(exn1, exn2, varGen, level, loc)

                _:
                    # In all other cases we have `None` as at least one of the
                    # types. `None` comes from a constructor, and constructors
                    # can't throw. So we let these unify.
                    ()

            unify(ret1, ret2, varGen, level, loc)

        (
            ty1 =
                Ty.Anonymous(
                    labels = labels1,
                    extension = extension1,
                    kind = kind1,
                    isRow = isRow1
                ),
            ty2 =
                Ty.Anonymous(
                    labels = labels2,
                    extension = extension2,
                    kind = kind2,
                    isRow = isRow2
                ),
        ): panic("TODO")

        _: throw(UnificationError)


unifyOneWay(ty1: Ty, ty2: Ty, varGen: UVarGen, level: U32, loc: Loc) / UnificationError:
    panic("TODO")


# TODO: This can't be `UVar.link` as `link` is also a field.
# Maybe for now rename the field (add underscore).
linkVar(var_: UVar, ty: Ty):
    # TODO: Occurs check.
    # TODO: Debug assert that link is `None`?
    ty.pruneLevel(var_.level)
    var_.link = Option.Some(ty)


Ty.pruneLevel(self, maxLevel: U32):
    match self:
        Ty.Con(..): ()

        Ty.App(args, ..):
            for arg: Ty in args.iter():
                arg.pruneLevel(maxLevel)

        Ty.QVar(..): panic("QVar in pruneLevel")

        Ty.UVar(uvar): uvar.pruneLevel(maxLevel)

        Ty.RVar(..): ()

        Ty.Fun(args, ret, exn):
            match args:
                FunArgs.Positional(tys):
                    for ty: Ty in tys.iter():
                        ty.pruneLevel(maxLevel)

                FunArgs.Named(tys):
                    for ty: Ty in tys.values():
                        ty.pruneLevel(maxLevel)

            ret.pruneLevel(maxLevel)

            if exn is Option.Some(exn):
                exn.pruneLevel(maxLevel)

        Ty.Anonymous(labels, extension, ..):
            for ty: Ty in labels.values():
                ty.pruneLevel(maxLevel)

            if extension is Option.Some(extension):
                extension.pruneLevel(maxLevel)


UVar.pruneLevel(self, maxLevel: U32):
    self.level = min(self.level, maxLevel)
