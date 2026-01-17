import [
    Compiler/Ast,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/Ty,
]


## Convert an AST type to type checking type.
convertAstTy(module: Module, vars: ScopeMap[Str, Ty], astTy: Type) Ty / TypeError:
    let loc = module.loc(astTy)
    match astTy:
        Type.Named(namedTy): convertNamedTy(module, vars, namedTy, loc)

        Type.Var(var_):
            let varText = module.idText(var_)
            vars.get(varText).unwrapOrElse(
                \():
                    throw(
                        TypeError(loc, msg = "Unbound type variable `varText`",),
                    ),
            )

        Type.Record(RecordType(fields, extension, isRow, ..)):
            let labels: HashMap[LocalId, Ty] = HashMap.withCapacity(fields.len())

            for namedField: Named[Type] in fields.iter():
                let name = module.idText(
                    namedField.name.unwrapOrElse(
                        \():
                            throw(
                                TypeError(
                                    loc,
                                    msg =
                                        "Records with unnamed fields not supported yet",
                                ),
                            ),
                    ),
                )
                let ty = convertAstTy(module, vars, namedField.node)
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
                \(extId):
                    let extIdText = module.idText(extId)
                    vars.get(extIdText).unwrapOrElse(
                        \():
                            throw(
                                TypeError(
                                    loc,
                                    msg = "Unbound type variable `extIdText`",
                                ),
                            ),
                    ),
            )

            Ty.Record(labels, extension, isRow)

        Type.Variant(VariantType(alts, extension, isRow, ..)):
            let cons: HashMap[TyDefIdx, Vec[Ty]] = HashMap.withCapacity(
                alts.len(),
            )

            for alt: NamedType in alts.iter():
                let ty = convertNamedTy(module, vars, alt, loc)

                match ty:
                    Ty.Con(id):
                        let old = cons.insert(id, Vec.empty())
                        if old is Option.Some(_):
                            throw(
                                TypeError(
                                    loc,
                                    msg =
                                        "Type `alt.name.name` used multiple times in variant type",
                                ),
                            )

                    Ty.App(conId, args):
                        let old = cons.insert(conId, Vec.empty())
                        if old is Option.Some(_):
                            throw(
                                TypeError(
                                    loc,
                                    msg =
                                        "Type `alt.name.name` used multiple times in variant type",
                                ),
                            )

                    other:
                        throw(
                            TypeError(
                                loc,
                                msg =
                                    "Variants can't have type variables, functions, records, variants as alternatives",
                            ),
                        )

            let extension = extension.map(
                \(extId):
                    let extIdText = module.idText(extId)
                    vars.get(extIdText).unwrapOrElse(
                        \():
                            throw(
                                TypeError(
                                    loc,
                                    msg = "Unbound type variable `extIdText`",
                                ),
                            ),
                    ),
            )

            Ty.Variant(cons, extension, isRow,)

        Type.Fn_(FnType(args, ret, exceptions, ..)):
            let args = FunArgs.Positional(
                Vec.fromIter(
                    args.iter().map(
                        \(ty: Type) Ty: convertAstTy(module, vars, ty),
                    ),
                ),
            )

            let ret = match ret:
                Option.None: Ty.unit()
                Option.Some(ret): convertAstTy(module, vars, ret)

            let exceptions = exceptions.unwrapOrElse(
                \():
                    throw(
                        TypeError(
                            loc,
                            msg = "Function type without exception type",
                        ),
                    ),
            )

            let exceptions = convertAstTy(module, vars, exceptions)

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
        print(tyCon.toDoc().render(80))
        throw(
            TypeError(
                loc,
                msg =
                    "Incorrect number of type arguments to `tyName`, expected `tyCon
                        .info.arity()`, found `numTyArgs`",
            ),
        )

    if numTyArgs == 0:
        return Ty.Con(id = tyDefIdx)

    let convertedArgs: Vec[Ty] = Vec.fromIter(
        tyArgs.unwrap().args.iter().map(
            \(astTy: Type) Ty: convertAstTy(module, vars, astTy),
        ),
    )

    Ty.App(conId = tyDefIdx, args = convertedArgs)


convertFields(module: Module, vars: ScopeMap[Str, Ty], fields: ConFields) Option[FunArgs] / TypeError:
    match fields:
        ConFields.Empty: Option.None

        ConFields.Named(namedFields):
            Option.Some(
                FunArgs.Named(
                    HashMap.fromIter(
                        namedFields.iter().map(
                            \(field: NamedField) (key: LocalId, val: Ty):
                                (
                                    key =
                                        LocalId(name = module.idText(field.name)),
                                    val = convertAstTy(module, vars, field.ty),
                                ),
                        ),
                    ),
                ),
            )

        ConFields.Unnamed(fields):
            Option.Some(
                FunArgs.Positional(
                    Vec.fromIter(
                        fields.iter().map(
                            \(ty: Type) Ty: convertAstTy(module, vars, ty),
                        ),
                    ),
                ),
            )


type TyVarConversion:
    ToRVar
    ToQVar


## Convert the context to type checking types, update `vars` (in the current
## scope) with the context types.
convertAndBindContext(
    module: Module,
    vars: ScopeMap[Str, Ty],
    typeParams: Vec[TypeParam],
    preds: Vec[Type],
    conversion: TyVarConversion,
) Vec[Pred] / TypeError:
    let predsConverted: Vec[Pred] = Vec.withCapacity(preds.len())

    # Bind type parameters.
    for tyParam: TypeParam in typeParams.iter():
        let var_ = match conversion:
            TyVarConversion.ToRVar:
                Ty.RVar(RVar(id = tyParam.name, kind = tyParam.kind,))
            TyVarConversion.ToQVar:
                Ty.QVar(QVar(id = tyParam.name, kind = tyParam.kind,))
        vars.insert(tyParam.name.name, var_)

    # Convert preds.
    for pred: Type in preds.iter():
        let loc = module.loc(pred)
        let pred = match convertAstTy(module, vars, pred):
            Ty.App(conId, args): Pred(trait_ = conId, params = args, loc)
            other: panic("Strange predicate syntax")
        predsConverted.push(pred)

    predsConverted
