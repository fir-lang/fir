import [
    Compiler/Ast,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/Ty,
]


## Convert an AST type to type checking type.
convertAstTy(module: Module, vars: ScopeMap[Str, Ty], astTy: Type, loc: Loc) Ty / TypeError:
    match astTy:
        Type.Named(namedTy): convertNamedTy(module, vars, namedTy, loc)

        Type.Var(var_):
            let varText = module.idText(var_)
            vars.get(varText).unwrapOrElse(
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
                let ty = convertAstTy(module, vars, namedField.node, loc)
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
                    vars.get(extIdText).unwrapOrElse(
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

        Type.Variant(VariantType(alts, extension, isRow, ..)):
            let labels: HashMap[LocalId, Ty] = HashMap.withCapacity(alts.len())

            for alt: NamedType in alts.iter():
                let ty = convertNamedTy(module, vars, alt, loc)
                let tyNameText = alt.name.name
                let old = labels.insert(LocalId(name = tyNameText), ty)
                if old is Option.Some(_):
                    throw(
                        TypeError(
                            loc,
                            msg =
                                "Type `tyNameText` used multiple times in variant type",
                        ),
                    )

            let extension = extension.map(
                |extId|:
                    let extIdText = module.idText(extId)
                    vars.get(extIdText).unwrapOrElse(
                        ||:
                            throw(
                                TypeError(
                                    loc,
                                    msg = "Unbound type variable `extIdText`",
                                ),
                            ),
                    ),
            )

            Ty.Anonymous(
                labels,
                extension,
                kind = RecordOrVariant.Variant,
                isRow,
            )

        Type.Fn_(FnType(args, ret, exceptions, ..)):
            let args = FunArgs.Positional(
                Vec.fromIter(
                    args.iter().map(
                        |ty: Type| Ty: convertAstTy(module, vars, ty, loc),
                    ),
                ),
            )

            let ret = match ret:
                Option.None: Ty.unit()
                Option.Some(ret): convertAstTy(module, vars, ret, loc)

            let exceptions = exceptions.unwrapOrElse(
                ||:
                    throw(
                        TypeError(
                            loc,
                            msg = "Function type without exception type",
                        ),
                    ),
            )

            let exceptions = convertAstTy(module, vars, exceptions, loc)

            Ty.Fun(args, ret, exn = Option.Some(exceptions))


convertNamedTy(
    module: Module,
    vars: ScopeMap[Str, Ty],
    namedTy: NamedType,
    loc: Loc,
) Ty / TypeError:
    let tyName = namedTy.name.name
    let tyArgs = namedTy.args
    let numTyArgs = namedTy.numTyArgs()

    let tyDefIdx = namedTy.name.def()
    let tyDefName = tyDefIdx._name

    let tyCon = module._tcEnv.unwrap()._cons.get(tyDefName).unwrap()

    if tyCon.info.arity() != numTyArgs:
        throw(
            TypeError(
                loc,
                msg =
                    "Incorrect number of type arguments to `tyName`, expected `tyCon.info.arity()`, found `numTyArgs`",
            ),
        )

    if numTyArgs == 0:
        return Ty.Con(id = tyDefIdx)

    let convertedArgs: Vec[Ty] = Vec.fromIter(
        tyArgs.unwrap().args.iter().map(
            |astTy: Type| Ty: convertAstTy(module, vars, astTy, loc),
        ),
    )

    Ty.App(conId = tyDefIdx, args = convertedArgs)


type TyVarConversion:
    ToRVar
    ToQVar


## Convert the context to type checking types, update `vars` (in the current
## scope) with the context types.
convertAndBindContext(
    module: Module,
    vars: ScopeMap[Str, Ty],
    contextAst: Context,
    conversion: TyVarConversion,
) Vec[Pred] / TypeError:
    let predsConverted: Vec[Pred] = Vec.withCapacity(contextAst.preds.len())

    # Bind type parameters.
    for tyParam: TypeParam in contextAst.typeParams.iter():
        let varText = module.idText(tyParam.name)
        let var_ = match conversion:
            TyVarConversion.ToRVar:
                Ty.RVar(RVar(id = LocalId(name = varText), kind = tyParam.kind,))
            TyVarConversion.ToQVar:
                Ty.QVar(QVar(id = LocalId(name = varText), kind = tyParam.kind,))
        vars.insert(varText, var_)

    # Convert preds.
    for pred: Type in contextAst.preds.iter():
        # TODO: get token loc from module
        let loc = Loc(file = "", line = 0, col = 0)
        let pred = match convertAstTy(module, vars, pred, loc):
            Ty.App(conId, args): Pred(trait_ = conId, params = args, loc)
            other: panic("Strange predicate syntax")
        predsConverted.push(pred)

    predsConverted
