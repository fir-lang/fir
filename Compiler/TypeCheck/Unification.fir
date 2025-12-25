import [
    Compiler/Assert,
    Compiler/Error,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/Normalization,
    Compiler/TypeCheck/RowUtils,
    Compiler/TypeCheck/Ty,
]


unify(ty1: Ty, ty2: Ty, varGen: UVarGen, level: U32, loc: Loc) / TypeError:
    ty1 = ty1.normalize()
    ty2 = ty2.normalize()

    match (ty1 = ty1, ty2 = ty2):
        (ty1 = Ty.Con(id = id1), ty2 = Ty.Con(id = id2)):
            if id1 != id2:
                throw(
                    TypeError(
                        loc,
                        msg = "Unable to unify types `ty1` and `ty2`",
                    ),
                )

        (
            ty1 = Ty.App(conId = id1, args = args1),
            ty2 = Ty.App(conId = id2, args = args2),
        ):
            if id1 != id2:
                throw(
                    TypeError(
                        loc,
                        msg = "Unable to unify types `ty1` and `ty2`",
                    ),
                )

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
                throw(
                    TypeError(
                        loc,
                        msg =
                            "Unable to unify var with kind `var1.kind` with type with kind `ty2
                                .kind()`",
                    ),
                )

            linkVar(var1, ty2)

        (ty1 = ty1, ty2 = Ty.UVar(var2)):
            if var2.kind != ty1.kind():
                throw(
                    TypeError(
                        loc,
                        msg =
                            "Unable to unify var with kind `var2.kind` with type with kind `ty1
                                .kind()`",
                    ),
                )

            linkVar(var2, ty1)

        (
            ty1 = Ty.Fun(args = args1, ret = ret1, exn = exn1),
            ty2 = Ty.Fun(args = args2, ret = ret2, exn = exn2),
        ):
            if args1.len() != args2.len():
                throw(
                    TypeError(
                        loc,
                        msg =
                            "Unable to unify functions `ty1` and `ty2` (argument numbers don't match)",
                    ),
                )

            match (args1 = args1, args2 = args2):
                (
                    args1 = FunArgs.Positional(args1),
                    args2 = FunArgs.Positional(args2),
                ):
                    for argIdx: U32 in range(u32(0), args1.len()):
                        unify(
                            args1.get(argIdx),
                            args2.get(argIdx),
                            varGen,
                            level,
                            loc,
                        )

                (args1 = FunArgs.Named(args1), args2 = FunArgs.Named(args2)):
                    for arg1: HashMapEntry[LocalId, Ty] in args1.iter():
                        let arg2 = args2.get(arg1.key).unwrapOrElse(
                            \():
                                throw(
                                    TypeError(
                                        loc,
                                        msg =
                                            "Unable to unify functions with different named arguments",
                                    ),
                                ),
                        )
                        unify(arg1.value, arg2, varGen, level, loc)

                _:
                    throw(
                        TypeError(
                            loc,
                            msg =
                                "Unable to unify functions with positional and named arguments",
                        ),
                    )

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
                Ty.Record(
                    labels = labels1,
                    extension = extension1,
                    isRow = isRow1,
                ),
            ty2 =
                Ty.Record(
                    labels = labels2,
                    extension = extension2,
                    isRow = isRow2,
                ),
        ):
            if isRow1 != isRow2:
                throw(
                    TypeError(
                        loc,
                        msg = "Unable to unify row and non-row records",
                    ),
                )

            let (rows = labels1, extension = extension1) = collectRecordFields(
                ty1,
                labels1,
                extension1,
            )

            let (rows = labels2, extension = extension2) = collectRecordFields(
                ty2,
                labels2,
                extension2,
            )

            let keys1: HashSet[LocalId] = HashSet.fromIter(labels1.keys())
            let keys2: HashSet[LocalId] = HashSet.fromIter(labels2.keys())

            # Unify common labels.
            for key: LocalId in keys1.intersection(keys2):
                unify(
                    labels1.get(key).unwrap(),
                    labels2.get(key).unwrap(),
                    varGen,
                    level,
                    loc,
                )

            # Extra labels in one type will be added to the extension of the
            # other.
            let extras1: HashSet[LocalId] = HashSet.fromIter(
                keys1.difference(keys2),
            )
            let extras2: HashSet[LocalId] = HashSet.fromIter(
                keys2.difference(keys1),
            )

            # Add extras to rows.
            if not extras1.isEmpty():
                match extension2:
                    Option.Some(Ty.UVar(uvar)):
                        # TODO: Not sure about level
                        extension2 = Option.Some(
                            Ty.UVar(
                                linkRecordExtension(
                                    extras1,
                                    labels1,
                                    uvar,
                                    varGen,
                                    level,
                                    loc,
                                ),
                            ),
                        )
                    _:
                        throw(
                            TypeError(
                                loc,
                                msg =
                                    "Unable to unify record with fields `keys1` with record with fieldss `keys2`",
                            ),
                        )

            if not extras2.isEmpty():
                match extension1:
                    Option.Some(Ty.UVar(uvar)):
                        # TODO: Not sure about level
                        extension1 = Option.Some(
                            Ty.UVar(
                                linkRecordExtension(
                                    extras2,
                                    labels2,
                                    uvar,
                                    varGen,
                                    level,
                                    loc,
                                ),
                            ),
                        )
                    _:
                        throw(
                            TypeError(
                                loc,
                                msg =
                                    "Unable to unify record with fieldss `keys1` with record with fieldss `keys2`",
                            ),
                        )

            match (ext1 = extension1, ext2 = extension2):
                (ext1 = Option.None, ext2 = Option.None): ()

                (ext1 = Option.Some(ext1), ext2 = Option.None):
                    unify(ext1, Ty.unitRecordRow(), varGen, level, loc)

                (ext1 = Option.None, ext2 = Option.Some(ext2)):
                    unify(ext2, Ty.unitRecordRow(), varGen, level, loc)

                (ext1 = Option.Some(ext1), ext2 = Option.Some(ext2)):
                    unify(ext1, ext2, varGen, level, loc)

        (
            ty1 =
                Ty.Variant(cons = cons1, extension = extension1, isRow = isRow1,
                ),
            ty2 =
                Ty.Variant(cons = cons2, extension = extension2, isRow = isRow2,
                ),
        ):
            if isRow1 != isRow2:
                throw(
                    TypeError(
                        loc,
                        msg = "Unable to unify row and non-row variants",
                    ),
                )

            let (cons = cons1, extension = extension1) = collectVariantCons(
                ty1,
                cons1,
                extension1,
            )

            let (cons = cons2, extension = extension2) = collectVariantCons(
                ty2,
                cons2,
                extension2,
            )

            let keys1: HashSet[TyDefIdx] = HashSet.fromIter(cons1.keys())
            let keys2: HashSet[TyDefIdx] = HashSet.fromIter(cons2.keys())

            # Unify common labels.
            for key: TyDefIdx in keys1.intersection(keys2):
                unify(
                    Ty.app(key, cons1.get(key).unwrap()),
                    Ty.app(key, cons2.get(key).unwrap()),
                    varGen,
                    level,
                    loc,
                )

            # Extra labels in one type will be added to the extension of the
            # other.
            let extras1: HashSet[TyDefIdx] = HashSet.fromIter(
                keys1.difference(keys2),
            )

            let extras2: HashSet[TyDefIdx] = HashSet.fromIter(
                keys2.difference(keys1),
            )

            # Add extras to rows.
            if not extras1.isEmpty():
                match extension2:
                    Option.Some(Ty.UVar(uvar)):
                        # TODO: Not sure about level
                        extension2 = Option.Some(
                            Ty.UVar(
                                linkVariantExtension(
                                    extras1,
                                    cons1,
                                    uvar,
                                    varGen,
                                    level,
                                    loc,
                                ),
                            ),
                        )
                    _: throw(TypeError(loc, msg = "Unable to unify variants",),)

            if not extras2.isEmpty():
                match extension1:
                    Option.Some(Ty.UVar(uvar)):
                        # TODO: Not sure about level
                        extension1 = Option.Some(
                            Ty.UVar(
                                linkVariantExtension(
                                    extras2,
                                    cons2,
                                    uvar,
                                    varGen,
                                    level,
                                    loc,
                                ),
                            ),
                        )
                    _: throw(TypeError(loc, msg = "Unable to unify variants",),)

            match (ext1 = extension1, ext2 = extension2):
                (ext1 = Option.None, ext2 = Option.None): ()

                (ext1 = Option.Some(ext1), ext2 = Option.None):
                    unify(ext1, Ty.emptyVariantRow(), varGen, level, loc)

                (ext1 = Option.None, ext2 = Option.Some(ext2)):
                    unify(ext2, Ty.emptyVariantRow(), varGen, level, loc)

                (ext1 = Option.Some(ext1), ext2 = Option.Some(ext2)):
                    unify(ext1, ext2, varGen, level, loc)

        _:
            throw(
                TypeError(loc, msg = "Unable to unify types `ty1` and `ty2`",),
            )


## Unify `ty1` with `ty2`, without updating `t2`.
##
## Unlike `unify`, this does not throw on errors. Returns whether unification
## was successful.
#
# Currently this has two use cases:
#
# - When matching an `impl` arguments with given type arguments, to be able to
#   select implementation of a predicate. Here `ty1` is instantiated type
#   arguments of an `impl` and `ty2` is the argument we have from a trait type
#   application.
#
# - When selecting a method in a method call, we unify a candidate's receiver
#   type (`ty1`) with the actual receiver type (`ty2`). If the unification is
#   successful, we consider the method as a potential target.
#
unifyOneWay(ty1: Ty, ty2: Ty, varGen: UVarGen, level: U32, loc: Loc) Bool:
    ty1 = ty1.normalize()
    ty2 = ty2.normalize()

    match (ty1 = ty1, ty2 = ty2):
        (ty1 = Ty.Con(id = id1), ty2 = Ty.Con(id = id2)): id1 == id2

        (
            ty1 = Ty.App(conId = id1, args = args1),
            ty2 = Ty.App(conId = id2, args = args2),
        ):
            if id1 != id2:
                return Bool.False

            if args1.len() != args2.len():
                return Bool.False

            for argIdx: U32 in range(u32(0), args1.len()):
                if not unifyOneWay(
                        args1.get(argIdx),
                        args2.get(argIdx),
                        varGen,
                        level,
                        loc,
                    ):
                    return Bool.False

            Bool.True

        (ty1 = Ty.QVar(_), ..) | (ty2 = Ty.QVar(_), ..):
            panic("`loc`: BUG: QVar in unification")

        (ty1 = Ty.UVar(var1), ty2 = Ty.UVar(var2)):
            # TODO: Interpreter doesn't have kind check here.
            if var1.kind != ty2.kind():
                return Bool.False

            if var1 == var2:
                return Bool.True

            # TODO: Copied from the interpreter, this updates ty2. Is this
            # expected? We promise to not update ty2 in the documentation.
            if var1.level > var2.level:
                var1.setLink(ty2)
            else:
                var2.setLink(ty1)

            Bool.True

        (
            ty1 = Ty.Fun(args = args1, ret = ret1, exn = exn1),
            ty2 = Ty.Fun(args = args2, ret = ret2, exn = exn2),
        ):
            if args1.len() != args2.len():
                return Bool.False

            match (args1 = args1, args2 = args2):
                (
                    args1 = FunArgs.Positional(args1),
                    args2 = FunArgs.Positional(args2),
                ):
                    for argIdx: U32 in range(u32(0), args1.len()):
                        if not unifyOneWay(
                                args1.get(argIdx),
                                args2.get(argIdx),
                                varGen,
                                level,
                                loc,
                            ):
                            return Bool.False

                (args1 = FunArgs.Named(args1), args2 = FunArgs.Named(args2)):
                    let argNames1: HashSet[LocalId] = HashSet.fromIter(
                        args1.keys(),
                    )
                    let argNames2: HashSet[LocalId] = HashSet.fromIter(
                        args2.keys(),
                    )

                    if argNames1 != argNames2:
                        return Bool.False

                    for argName: LocalId in argNames1.iter():
                        if not unifyOneWay(
                                args1.get(argName).unwrap(),
                                args2.get(argName).unwrap(),
                                varGen,
                                level,
                                loc,
                            ):
                            return Bool.False

                _: return Bool.False

            match (exn1 = exn1, exn2 = exn2):
                (exn1 = Option.None, exn2 = Option.None): ()

                (exn1 = Option.None, exn2 = Option.Some(_))
                    | (exn1 = Option.Some(_), exn2 = Option.None):
                    # None is the same as [..r] with a fresh r, so it unifies
                    # with everything.
                    ()

                (exn1 = Option.Some(exn1), exn2 = Option.Some(exn2)):
                    if not unifyOneWay(exn1, exn2, varGen, level, loc):
                        return Bool.False

            unifyOneWay(ret1, ret2, varGen, level, loc)

        (
            ty1 =
                Ty.Record(
                    labels = labels1,
                    extension = extension1,
                    isRow = isRow1,
                ),
            ty2 =
                Ty.Record(
                    labels = labels2,
                    extension = extension2,
                    isRow = isRow2,
                ),
        ):
            # Kind mismatches can happen when try to unify a record with a
            # variant (e.g. pass a record when a variant is expected), and fail.
            if isRow1 != isRow2:
                return Bool.False

            let (rows = rows1, extension = extension1) = collectRecordFields(
                ty1,
                labels1,
                extension1,
            )

            let (rows = rows2, extension = extension2) = collectRecordFields(
                ty2,
                labels2,
                extension2,
            )

            let keys1: HashSet[LocalId] = HashSet.fromIter(labels1.keys())
            let keys2: HashSet[LocalId] = HashSet.fromIter(labels2.keys())

            # Extra labels in one type will be added to the extension of the
            # other.
            let extras1: HashSet[LocalId] = HashSet.fromIter(
                keys1.difference(keys2),
            )

            let extras2: HashSet[LocalId] = HashSet.fromIter(
                keys2.difference(keys1),
            )

            # Unify common labels.
            for key: LocalId in keys1.intersection(keys2):
                let ty1 = labels1.get(key).unwrap()
                let ty2 = labels2.get(key).unwrap()
                if not unifyOneWay(ty1, ty2, varGen, level, loc):
                    return Bool.False

            if not extras1.isEmpty():
                return Bool.False

            if not extras2.isEmpty():
                match extension1:
                    Option.Some(Ty.UVar(uvar)):
                        # TODO: Not sure about level
                        extension1 = Option.Some(
                            Ty.UVar(
                                linkRecordExtension(
                                    extras2,
                                    labels2,
                                    uvar,
                                    varGen,
                                    level,
                                    loc,
                                ),
                            ),
                        )
                    _: return Bool.False

            match (ext1 = extension1, ext2 = extension2):
                (ext1 = Option.None, ext2 = Option.None): Bool.True

                (ext1 = Option.Some(ext1), ext2 = Option.None):
                    unifyOneWay(ext1, Ty.unitRecordRow(), varGen, level, loc,)

                (ext1 = Option.None, ext2 = Option.Some(ext2)): Bool.False

                (ext1 = Option.Some(ext1), ext2 = Option.Some(ext2)):
                    unifyOneWay(ext1, ext2, varGen, level, loc)

        (
            ty1 =
                Ty.Variant(cons = cons1, extension = extension1, isRow = isRow1,
                ),
            ty2 =
                Ty.Variant(cons = cons2, extension = extension2, isRow = isRow2,
                ),
        ):
            if isRow1 != isRow2:
                return Bool.False

            let (cons = cons1, extension = extension1) = collectVariantCons(
                ty1,
                cons1,
                extension1,
            )

            let (cons = cons2, extension = extension2) = collectVariantCons(
                ty2,
                cons2,
                extension2,
            )

            let keys1: HashSet[TyDefIdx] = HashSet.fromIter(cons1.keys())
            let keys2: HashSet[TyDefIdx] = HashSet.fromIter(cons2.keys())

            # Unify common labels.
            for key: TyDefIdx in keys1.intersection(keys2):
                let ty1 = Ty.app(key, cons1.get(key).unwrap())
                let ty2 = Ty.app(key, cons2.get(key).unwrap())
                if not unifyOneWay(ty1, ty2, varGen, level, loc):
                    return Bool.False

            # Extra labels in one type will be added to the extension of the
            # other.
            let extras1: HashSet[TyDefIdx] = HashSet.fromIter(
                keys1.difference(keys2),
            )

            let extras2: HashSet[TyDefIdx] = HashSet.fromIter(
                keys2.difference(keys1),
            )

            if not extras1.isEmpty():
                return Bool.False

            if not extras2.isEmpty():
                match extension1:
                    Option.Some(Ty.UVar(uvar)):
                        # TODO: Not sure about level
                        extension1 = Option.Some(
                            Ty.UVar(
                                linkVariantExtension(
                                    extras2,
                                    cons2,
                                    uvar,
                                    varGen,
                                    level,
                                    loc,
                                ),
                            ),
                        )
                    _: return Bool.False

            match (ext1 = extension1, ext2 = extension2):
                (ext1 = Option.None, ext2 = Option.None): Bool.True

                (ext1 = Option.Some(ext1), ext2 = Option.None):
                    unifyOneWay(ext1, Ty.emptyVariantRow(), varGen, level, loc)

                (ext1 = Option.None, ext2 = Option.Some(ext2)): Bool.False

                (ext1 = Option.Some(ext1), ext2 = Option.Some(ext2)):
                    unifyOneWay(ext1, ext2, varGen, level, loc)

        _: Bool.False


# TODO: This can't be `UVar.link` as `link` is also a field.
# Maybe for now rename the field (add underscore).
linkVar(var_: UVar, ty: Ty):
    # TODO: Occurs check.
    ty.pruneLevel(var_.level)
    var_.setLink(ty)


linkRecordExtension(
    extraLabels: HashSet[LocalId],
    labelValues: HashMap[LocalId, Ty],
    uvar: UVar,
    varGen: UVarGen,
    level: U32,
    loc: Loc,
) UVar:
    let extensionLabels: HashMap[LocalId, Ty] = HashMap.fromIter(
        extraLabels.iter().map(
            \(label: LocalId):
                (key = label, value = labelValues.get(label).unwrap()),
        ),
    )

    # TODO: Not sure about the level.
    let newExtensionVar = varGen.newVar(
        level,
        Kind.Row(RecordOrVariant.Record),
        loc,
    )

    let newExtensionTy = Ty.Record(
        labels = extensionLabels,
        extension = Option.Some(Ty.UVar(newExtensionVar)),
        isRow = Bool.True,
    )

    uvar.setLink(newExtensionTy)
    newExtensionVar


linkVariantExtension(
    extraCons: HashSet[TyDefIdx],
    cons: HashMap[TyDefIdx, Vec[Ty]],
    uvar: UVar,
    varGen: UVarGen,
    level: U32,
    loc: Loc,
) UVar:
    let extensionCons: HashMap[TyDefIdx, Vec[Ty]] = HashMap.fromIter(
        extraCons.iter().map(
            \(label: TyDefIdx): (key = label, value = cons.get(label).unwrap()),
        ),
    )

    # TODO: Not sure about the level.
    let newExtensionVar = varGen.newVar(
        level,
        Kind.Row(RecordOrVariant.Variant),
        loc,
    )

    let newExtensionTy = Ty.Variant(
        cons = extensionCons,
        extension = Option.Some(Ty.UVar(newExtensionVar)),
        isRow = Bool.True,
    )

    uvar.setLink(newExtensionTy)
    newExtensionVar


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

        Ty.Variant(cons, extension, ..):
            for tys: Vec[Ty] in cons.values():
                for ty: Ty in tys.iter():
                    ty.pruneLevel(maxLevel)

            if extension is Option.Some(extension):
                extension.pruneLevel(maxLevel)

        Ty.Record(labels, extension, ..):
            for ty: Ty in labels.values():
                ty.pruneLevel(maxLevel)

            if extension is Option.Some(extension):
                extension.pruneLevel(maxLevel)


UVar.pruneLevel(self, maxLevel: U32):
    self.level = min(self.level, maxLevel)
