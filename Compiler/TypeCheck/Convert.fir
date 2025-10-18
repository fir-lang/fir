import [
    Compiler/Ast,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyMap,
]


convertAstTy(module: Module, tys: TyMap, astTy: Type, loc: Loc) Ty / TypeError:
    match astTy:
        Type.Named(namedTy): convertNamedTy(tys, namedTy, loc)

        Type.Var(var_):
            let varText = module.idText(var_)
            tys.getVar(varText).unwrapOrElse(
                ||:
                    throw(
                        TypeError(loc, msg = "Unbound type variable `varText`",),
                    ),
            )

        Type.Record(RecordType(fields, extension, isRow, ..)):
            let labels: HashMap[LocalId, Ty] = HashMap.withCapacity(fields.len())

            for namedField: Named[Type] in fields.iter():
                let name = module.idText(
                    namedField.name.unwrapOrElse(
                        ||:
                            throw(
                                TypeError(
                                    loc,
                                    msg =
                                        "Records with unnamed fields not supported yet",
                                ),
                            ),
                    ),
                )
                let ty = convertAstTy(module, tys, namedField.node, loc)
                let old = labels.insert(LocalId(name), ty)
                if old is Option.Some(_):
                    throw(
                        TypeError(
                            loc,
                            msg =
                                "Field `name` defined multiple times in record",
                        ),
                    )

            let extension = extension.map(
                |extId|:
                    let extIdText = module.idText(extId)
                    tys.getVar(extIdText).unwrapOrElse(
                        ||:
                            throw(
                                TypeError(
                                    loc,
                                    msg = "Unbound type variable `extIdText`",
                                ),
                            ),
                    ),
            )

            Ty.Anonymous(labels, extension, kind = RecordOrVariant.Record, isRow)

        Type.Variant(_): panic("TODO")

        Type.Fn_(_): panic("TODO")


convertNamedTy(tys: TyMap, namedTy: NamedType, loc: Loc) Ty:
    panic("TODO")
