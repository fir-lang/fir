# Import all modules temporarily to type check all.
import [
    Compiler/Program,
    Compiler/ScopeMap,
    Compiler/TypeCheck/Convert,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/Expr,
    Compiler/TypeCheck/KindInference,
    Compiler/TypeCheck/Normalization,
    Compiler/TypeCheck/RowUtils,
    Compiler/TypeCheck/TraitEnv,
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyCon,
    Compiler/TypeCheck/Unification,
]


prepTcEnvs(pgm: Program) / TypeError:
    # Prep `TyCon` envs in dependency order: from dependency SCCs to dependent
    # SCCs.
    #
    # In the future: we probably want to prep SCC envs on demand to allow
    # prepping only the needed envs. I.e. recursively prep envs, cache prepped
    # envs.
    for scc: HashSet[ModuleIdx] in pgm._depGraph.unwrap().iter():
        initSccTyCons(pgm, scc)

    # All modules have access to all `TyCon`s that they need, add `TyCon`
    # details.
    for modIdx: U32 in range(u32(0), pgm._modules.len()):
        addModTyConDetails(pgm, ModuleIdx(_idx = modIdx))

    # Create top-level function, associated function, and method schemes.
    # Note: this could be done for each SCC after updating `TyCon`s of an SCC,
    # in the previous loop. For now we keep it separate to make debugging
    # easier.
    for modIdx: U32 in range(u32(0), pgm._modules.len()):
        addModSchemes(pgm, ModuleIdx(_idx = modIdx))

    # Now that each module has its own schemes, add imported schemes. Similar to
    # the passes above, we need to initialize one SCC at a time as modules in a
    # SCC all have access to the same things for now.
    for scc: HashSet[ModuleIdx] in pgm._depGraph.unwrap().iter():
        addImportedSchemes(pgm, scc)

    # TODO: Populate method environments of modules with associated functions
    # with `self` arguments.
    ()


## Initialize `TyCon`s of modules in the given SCC.
##
## Dependency SCC `TyCon`s should already be initialized.
initSccTyCons(pgm: Program, sccModules: HashSet[ModuleIdx]):
    # Reminder: with the current import semantics each SCC has access to all of
    # the things in the SCC.
    #
    # However we still need per-module (rather than per-SCC) environments
    # because
    #
    # (1) the import paths of items available in each of the modules will be
    #     different.
    #
    # (2) in the future we will add imported item lists so the environments will
    #     be different in places other than just the import paths.

    # The way we create type envs for the modules of a SCC is similar to the way
    # we process the whole program in the interpreter (in multiple steps), but
    # with some differences to handle SCC modules importing each other.
    #
    # - Initialize types for each of the modules, without the details
    #   (`TyConDetails`).
    #
    # - Add type imports to modules in the SCCs.
    #
    # - At this point each of the module in the SCC has all of the types that
    #   they need, so add `TyConDetails`.
    #
    # - Initialize top-level, associated, and method schemes in each of the
    #   modules.
    #
    # - Add function imports to each of the modules.

    # Initialize empty type checking envs.
    for modIdx: ModuleIdx in sccModules.iter():
        let mod: Module = pgm._modules.get(modIdx._idx)
        assert(mod._tcEnv is Option.None)
        mod._tcEnv = Option.Some(ModuleTcEnv.empty())

    # Initialize types defined in the current SCC first.
    for modIdx: ModuleIdx in sccModules.iter():
        let mod: Module = pgm._modules.get(modIdx._idx)
        let modCons: HashMap[Str, TcItem[TyDefIdx, TyCon]] = mod._tcEnv.unwrap()
            ._cons
        let modTokens = mod._tokens

        for tyDecl: TypeDecl in mod._tyItems.values():
            let tyDeclName = mod.idText(tyDecl.name)
            let old = modCons.insert(
                tyDeclName,
                TcItem(
                    idx = mod._tyEnv.get(tyDeclName).unwrap(),
                    info =
                        TyCon(
                            name = tyDeclName,
                            tyParams =
                                Vec.fromIter(
                                    range(u32(0), tyDecl.typeParams.len()).map(
                                        |i: U32| TyParam:
                                            TyParam(
                                                name =
                                                    LocalId(
                                                        name =
                                                            mod.idText(
                                                                tyDecl
                                                                    .typeParams
                                                                    .get(i),
                                                            ),
                                                    ),
                                                kind =
                                                    tyDecl.typeParamKinds.get(i),
                                            ),
                                    ),
                                ),
                            details = TyConDetails.placeholder(),
                        ),
                    imports = HashSet.[modIdx],
                ),
            )
            assert(old is Option.None)

        for traitDecl: TraitDecl in mod._traitItems.values():
            let tyDeclName = mod.idText(traitDecl.name)
            let old = modCons.insert(
                tyDeclName,
                TcItem(
                    idx = mod._tyEnv.get(tyDeclName).unwrap(),
                    info =
                        TyCon(
                            name = tyDeclName,
                            tyParams =
                                Vec.fromIter(
                                    range(u32(0), traitDecl.typeParams.len())
                                        .map(
                                        |i: U32| TyParam:
                                            TyParam(
                                                name =
                                                    LocalId(
                                                        name =
                                                            mod.idText(
                                                                traitDecl
                                                                    .typeParams
                                                                    .get(i),
                                                            ),
                                                    ),
                                                kind =
                                                    traitDecl.typeParamKinds.get(
                                                        i,
                                                    ),
                                            ),
                                    ),
                                ),
                            details = TyConDetails.placeholder(),
                        ),
                    imports = HashSet.[modIdx],
                ),
            )
            assert(old is Option.None)

    # Add imports until none of the modules in the SCC import anything anymore.
    # Note: we could handle the imports from other SCCs first and then never
    # soncider them again in this loop. For now keep the cost simple (and more
    # obviously corret) at the cost of compile time performance.
    let updated = Bool.True
    while updated:
        updated = Bool.False

        for modIdx: ModuleIdx in sccModules.iter():
            let mod: Module = pgm._modules.get(modIdx._idx)
            let modCons = mod._tcEnv.unwrap()._cons
            for importedModIdx: ModuleIdx in mod._imports.iter():
                let importedMod = pgm._modules.get(importedModIdx._idx)
                let importedModuleCons = importedMod._tcEnv.unwrap()._cons
                for importedItemEntry: HashMapEntry[Str, TcItem[TyDefIdx, TyCon]] in
                        importedModuleCons.iter():
                    let importedItemName = importedItemEntry.key
                    let importedItem = importedItemEntry.value

                    # If a type with the name is already imported, it should
                    # have the same `TyDefIdx`.
                    match modCons.get(importedItemName):
                        Option.Some(existingItem):
                            if existingItem.idx != importedItem.idx:
                                panic(
                                    "Type `importedItemName` imported/defined multiple times in `mod._filePath`",
                                )

                            let new = existingItem.imports.insert(importedModIdx)

                            # Note: we don't have `|=` syntax yet for `updated |= new`.
                            if new:
                                updated = Bool.True

                        Option.None:
                            modCons.insert(
                                importedItemName,
                                TcItem(
                                    idx = importedItem.idx,
                                    info = importedItem.info,
                                    imports = HashSet.[importedModIdx],
                                ),
                            )
                            updated = Bool.True


## After `TyCon`s of the module has been initialized (including imported
## `TyCon`s): add the details to the module's own `TyCon`s.
addModTyConDetails(pgm: Program, modIdx: ModuleIdx) / TypeError:
    let mod = pgm._modules.get(modIdx._idx)
    let tcEnv = mod._tcEnv.unwrap()

    for tyDecl: TypeDecl in mod._tyItems.values():
        let tyDeclName = mod.idText(tyDecl.name)
        let tyCon = tcEnv._cons.get(tyDeclName).unwrap()
        let details = TyConDetails.Type(
            TypeDetails(
                cons =
                    match tyDecl.rhs:
                        Option.Some(TypeDeclRhs.Sum(cons)):
                            Vec.fromIter(
                                cons.iter().map(
                                    |con: ConDecl| Str: mod.idText(con.name),
                                ),
                            )
                        Option.Some(TypeDeclRhs.Product(_fields)):
                            Vec.[tyDeclName]
                        Option.None: Vec.[],
                sum =
                    not (tyDecl.rhs is Option.Some(TypeDeclRhs.Product(_fields))),
            ),
        )
        tyCon.info.details = details

    for traitDecl: TraitDecl in mod._traitItems.values():
        let tyDeclName = mod.idText(traitDecl.name)
        let tyCon = tcEnv._cons.get(tyDeclName).unwrap()
        let varMap: ScopeMap[Str, Ty] = ScopeMap.empty()

        # TODO: This doesn't hold, need to add kinds.
        assert(traitDecl.typeParams.len() == traitDecl.typeParamKinds.len())

        let traitContext: Vec[Pred] = convertAndBindContext(
            mod,
            varMap,
            Vec.fromIter(
                range(u32(0), traitDecl.typeParams.len()).map(
                    |i: U32| TypeParam:
                        TypeParam(
                            name =
                                LocalId(
                                    name =
                                        mod.idText(traitDecl.typeParams.get(i)),
                                ),
                            kind = traitDecl.typeParamKinds.get(i),
                        ),
                ),
            ),
            Vec.empty(),
            TyVarConversion.ToQVar,
        )

        assert(traitContext.isEmpty())

        let methods: HashMap[Str, TraitMethod] = HashMap.empty()

        for method: FunDecl in traitDecl.items.iter():
            varMap.enterScope()

            # Note: this doesn't bind the implicit exception type (when the
            # signature doesn't have an exception type specified). That's OK
            # because the implicit type cannot be referred to in the function
            # body.
            let funPreds: Vec[Pred] = convertAndBindContext(
                mod,
                varMap,
                method.sig.typeParams,
                match method.sig.context:
                    Option.None: Vec.empty()
                    Option.Some(context): context.preds,
                TyVarConversion.ToQVar,
            )

            let numQVars = traitDecl.typeParams.len()
                + method.sig.typeParams.len()

            # Not specifying the exception type is the same as having a fresh
            # type variable for the exception type.
            if method.sig.exceptions is Option.None:
                numQVars += 1

            let schemeQVars: Vec[QVar] = Vec.withCapacity(numQVars)

            for traitTyArgIdx: U32 in range(u32(0), traitDecl.typeParams.len()):
                schemeQVars.push(
                    QVar(
                        id =
                            LocalId(
                                name =
                                    mod.idText(
                                        traitDecl.typeParams.get(traitTyArgIdx),
                                    ),
                            ),
                        kind = traitDecl.typeParamKinds.get(traitTyArgIdx),
                    ),
                )

            for tyParam: TypeParam in method.sig.typeParams.iter():
                schemeQVars.push(QVar(id = tyParam.name, kind = tyParam.kind))

            if method.sig.exceptions is Option.None:
                # The name we invent for the exception type does not matter as
                # it can't be used in the function body. It's also OK to not
                # bind it in `convertAndBindContext` above for the same reason.
                schemeQVars.push(
                    QVar(id = LocalId(name = "?exn"), kind = Kind.Star),
                )

            let argTys: Vec[Ty] = Vec.fromIter(
                method.sig.params.iter().map(
                    |param: FunArg| Ty:
                        let ty = param.ty.unwrap()
                        convertAstTy(mod, varMap, ty),
                ),
            )

            match method.sig.self_:
                SelfParam.No: ()
                SelfParam.Implicit:
                    panic("Trait methods can't have implicit self type")
                SelfParam.Explicit(ty):
                    argTys.insert(0, convertAstTy(mod, varMap, ty))

            let retTy: Ty = match method.sig.returnTy:
                Option.None: Ty.unit()
                Option.Some(retTy): convertAstTy(mod, varMap, retTy)

            let exnTy: Ty = match method.sig.exceptions:
                Option.None: Ty.QVar(schemeQVars.last().unwrap())
                Option.Some(retTy): convertAstTy(mod, varMap, retTy)

            varMap.exitScope()
            assert(varMap.lenScopes() == 1)

            let funTy = Ty.Fun(
                args = FunArgs.Positional(argTys),
                ret = retTy,
                exn = Option.Some(exnTy),
            )

            let scheme = Scheme(
                qvars = schemeQVars,
                preds = funPreds,
                ty = funTy,
                loc = mod.loc(method),
            )

            let old = methods.insert(
                mod.idText(method.name),
                TraitMethod(scheme, funDecl = method),
            )
            assert(old is Option.None)

        tyCon.info.details = TyConDetails.Trait(TraitDetails(methods))


## Update module type checking environment with top-level and associated
## function schemes for the functions defined in the module.
addModSchemes(pgm: Program, modIdx: ModuleIdx) / TypeError:
    let mod = pgm._modules.get(modIdx._idx)
    let tcEnv = mod._tcEnv.unwrap()

    for topFun: FunDecl in mod._funItems.values():
        let varMap: ScopeMap[Str, Ty] = ScopeMap.empty()

        let funPreds: Vec[Pred] = convertAndBindContext(
            mod,
            varMap,
            topFun.sig.typeParams,
            topFun.sig.context.map(|ctx: Context|: ctx.preds).unwrapOr(
                Vec.empty(),
            ),
            TyVarConversion.ToQVar,
        )

        let numQVars = topFun.sig.typeParams.len()

        # Not specifying the exception type is the same as having a fresh
        # type variable for the exception type.
        if topFun.sig.exceptions is Option.None:
            numQVars += 1

        let schemeQVars: Vec[QVar] = Vec.withCapacity(numQVars)

        for tyParam: TypeParam in topFun.sig.typeParams.iter():
            schemeQVars.push(QVar(id = tyParam.name, kind = tyParam.kind))

        if topFun.sig.exceptions is Option.None:
            # The name we invent for the exception type does not matter as
            # it can't be used in the function body. It's also OK to not
            # bind it in `convertAndBindContext` above for the same reason.
            schemeQVars.push(
                QVar(id = LocalId(name = "?exn"), kind = Kind.Star),
            )

        let argTys: Vec[Ty] = Vec.fromIter(
            topFun.sig.params.iter().map(
                |param: FunArg| Ty:
                    let ty = param.ty.unwrap()
                    convertAstTy(mod, varMap, ty),
            ),
        )

        match topFun.sig.self_:
            SelfParam.No: ()
            SelfParam.Implicit:
                # Parent type should have no type arguments.
                match topFun.parentTy:
                    Option.None:
                        # TODO: location should be the `self` location, but we
                        # don't have easy access to it yet.
                        throw(
                            TypeError(
                                loc = mod.tokenLoc(topFun.name.token),
                                msg =
                                    "Function with \`self\` parameter should be an associated type or method",
                            ),
                        )
                    Option.Some(parentTy):
                        let parentTyDef = parentTy.def()
                        let parentTyCon = pgm.tyCon(parentTyDef)
                        if not parentTyCon.tyParams.isEmpty():
                            throw(
                                TypeError(
                                    loc = mod.tokenLoc(topFun.name.token),
                                    msg =
                                        "Function \`self\` type needs type annotation",
                                ),
                            )
                        argTys.insert(0, Ty.Con(id = parentTyDef))
            SelfParam.Explicit(ty):
                argTys.insert(0, convertAstTy(mod, varMap, ty))

        let retTy: Ty = match topFun.sig.returnTy:
            Option.None: Ty.unit()
            Option.Some(retTy): convertAstTy(mod, varMap, retTy)

        let exnTy: Ty = match topFun.sig.exceptions:
            Option.None: Ty.QVar(schemeQVars.last().unwrap())
            Option.Some(retTy): convertAstTy(mod, varMap, retTy)

        assert(varMap.lenScopes() == 1)

        let funTy = Ty.Fun(
            args = FunArgs.Positional(argTys),
            ret = retTy,
            exn = Option.Some(exnTy),
        )

        let scheme = Scheme(
            qvars = schemeQVars,
            preds = funPreds,
            ty = funTy,
            loc = mod.loc(topFun),
        )

        let funName = mod.idText(topFun.name)

        match topFun.parentTy:
            Option.Some(parentTy):
                let parentTyName = parentTy.name

                let assocFunMap = match tcEnv._assocFnSchemes.get(parentTyName):
                    Option.Some(methods): methods
                    Option.None:
                        let methods: HashMap[Str, TcItem[AssocVarDefIdx, Scheme]] = HashMap
                            .withCapacity(10)
                        tcEnv._assocFnSchemes.insert(parentTyName, methods)
                        methods

                let old = assocFunMap.insert(
                    funName,
                    TcItem(
                        idx =
                            mod._assocTermEnv.get(parentTyName).unwrap().get(
                                funName,
                            ).unwrap(),
                        info = scheme,
                        imports = HashSet.[modIdx],
                    ),
                )

            Option.None:
                let old = tcEnv._topSchemes.insert(
                    funName,
                    TcItem(
                        idx = mod._termEnv.get(funName).unwrap(),
                        info = scheme,
                        imports = HashSet.[modIdx],
                    ),
                )
                if old is Option.Some(..):
                    throw(
                        TypeError(
                            loc = mod.tokenLoc(topFun.name.token),
                            msg =
                                "Top-level function \``funName`\` defined multiple times",
                        ),
                    )


## Update SCC modules with imported top-level and associated function schemes.
##
## Dependency SCCs should already be processed.
addImportedSchemes(pgm: Program, sccModules: HashSet[ModuleIdx]):
    let updated = Bool.True
    while updated:
        updated = Bool.False

        for modIdx: ModuleIdx in sccModules.iter():
            let mod = pgm._modules.get(modIdx._idx)
            let modTcEnv = mod._tcEnv.unwrap()
            for importedModIdx: ModuleIdx in mod._imports.iter():
                let importedMod = pgm._modules.get(importedModIdx._idx)
                let importedModTcEnv = importedMod._tcEnv.unwrap()

                # Import top-level functions.
                for topFun: HashMapEntry[Str, TcItem[TopVarDefIdx, Scheme]] in
                        importedModTcEnv._topSchemes.iter():
                    match modTcEnv._topSchemes.get(topFun.key):
                        Option.Some(existingItem):
                            if existingItem.idx != topFun.value.idx:
                                panic(
                                    "Type `topFun.key` imported/defined multiple times in `mod._filePath`",
                                )

                            let new = existingItem.imports.insert(importedModIdx)

                            if new:
                                updated = Bool.True

                        Option.None:
                            modTcEnv._topSchemes.insert(
                                topFun.key,
                                TcItem(
                                    idx = topFun.value.idx,
                                    info = topFun.value.info,
                                    imports = HashSet.[importedModIdx],
                                ),
                            )

                            updated = Bool.True

                # Import associated functions.
                for assocFunMap: HashMapEntry[Str, HashMap[Str, TcItem[AssocVarDefIdx, Scheme]]] in
                        modTcEnv._assocFnSchemes.iter():
                    let typeFunMap = match modTcEnv._assocFnSchemes.get(
                                    assocFunMap.key,
                                ):
                        Option.None:
                            let typeFunMap: HashMap[Str, TcItem[AssocVarDefIdx, Scheme]] = HashMap
                                .withCapacity(10)
                            modTcEnv._assocFnSchemes.insert(
                                assocFunMap.key,
                                typeFunMap,
                            )
                            typeFunMap
                        Option.Some(typeFunMap): typeFunMap

                    for fun: HashMapEntry[Str, TcItem[AssocVarDefIdx, Scheme]] in
                            assocFunMap.value.iter():
                        match typeFunMap.get(fun.key):
                            Option.Some(existingItem):
                                if existingItem.idx != fun.value.idx:
                                    panic(
                                        "Type `assocFunMap.key`.`fun.key` imported/defined multiple times in `mod._filePath`",
                                    )

                                let new = existingItem.imports.insert(
                                    importedModIdx,
                                )

                                if new:
                                    updated = Bool.True

                            Option.None:
                                typeFunMap.insert(
                                    fun.key,
                                    TcItem(
                                        idx = fun.value.idx,
                                        info = fun.value.info,
                                        imports = HashSet.[importedModIdx],
                                    ),
                                )
                                updated = Bool.True


# ------------------------------------------------------------------------------
# Module type checking environment


## The module environment holds type constructors, traits (with impls), and
## associated and top-level functions available in the module.
#[derive(ToDoc)]
type ModuleTcEnv(
    ## The traits, with impls.
    _traitEnv: TraitEnv,

    ## Type constructors.
    _cons: HashMap[Str, TcItem[TyDefIdx, TyCon]],

    ## Top-level function schemes.
    _topSchemes: HashMap[Str, TcItem[TopVarDefIdx, Scheme]],

    ## Associated function schemes.
    _assocFnSchemes: HashMap[Str, HashMap[Str, TcItem[AssocVarDefIdx, Scheme]]],

    ## Type schemes of methods.
    ##
    ## Maps method names to (type or trait name, type scheme) pairs.
    ##
    ## These are associated functions (so they're also in
    ## `associated_fn_schemes`) that take a `self` parameter.
    ##
    ## The first parameters of the function types here are the `self` types.
    ##
    ## Because these schemes are only used in method call syntax, the keys are
    ## not type names but method names. The values are type schemes of methods
    ## with the name.
    _methodSchemes: HashMap[Str, Vec[(id: Str, scheme: Scheme)]],
)


## An item (function, associated function, method, type, trait) defined
## somewhere in the program. (current module or imported)
#[derive(ToDoc)]
type TcItem[idx, info](
    ## Reference to the definition of the item.
    idx: idx,

    ## The details of the definition we need to type check a module.
    ##
    ## For functions this will be the type scheme of the function.
    ##
    ## For types this will be the type info:
    ## - Constructors (and fields etc.) of types
    ## - Methods of traits
    ## - Kinds
    ## - etc.
    info: info,

    ## Modules the item was imported from.
    ##
    ## An item can be imported from different modules. This will have all of
    ## those imported modules.
    ##
    ## For items defined in the current module this will have just one element,
    ## the defining module.
    imports: HashSet[ModuleIdx],
)


ModuleTcEnv.empty() ModuleTcEnv:
    ModuleTcEnv(
        _traitEnv = TraitEnv.empty(),
        _cons = HashMap.empty(),
        _topSchemes = HashMap.empty(),
        _assocFnSchemes = HashMap.empty(),
        _methodSchemes = HashMap.empty(),
    )


# ------------------------------------------------------------------------------
# Function type checking environment


## Type checking state for a single function (top-level, associated, or method).
type FunTcEnv(
    _modEnv: ModuleTcEnv,

    _termEnv: ScopeMap[Str, Ty],

    ## Unification variable generator.
    _varGen: UVarGen,

    ## Exception type of the current function.
    ##
    ## Exceptions thrown by called functions are unified with this type.
    ##
    ## For now we don't do exception type inference, so this will always be a
    ## concrete type (with rigid type variables).
    _exnTy: Ty,

    ## Return type of the current function.
    ##
    ## This is used when checking expressions in return positions and in
    ## `return` expressions.
    _retTy: Ty,

    ## Predicates generated when checking the function body.
    ##
    ## After checking the body, these predicates should all be resolved with the
    ## function context and trait environment.
    ##
    ## This is a `Vec` instead of `HashSet` as the type checker never visits an
    ## expression twice, so every `Pred` here will have a different `Loc`.
    _preds: Vec[Pred],

    ## The function context.
    _assumps: Vec[Pred],
)


FunTcEnv.new(modEnv: ModuleTcEnv, exnTy: Ty, retTy: Ty, assumps: Vec[Pred]) FunTcEnv:
    FunTcEnv(
        _modEnv = modEnv,
        _termEnv = ScopeMap.empty(),
        _varGen = UVarGen.new(),
        _exnTy = exnTy,
        _retTy = retTy,
        _preds = Vec.withCapacity(10),
        _assumps = assumps,
    )


FunTcEnv.local(self, local: Str) Ty:
    self._termEnv.get(local).unwrap()


# ------------------------------------------------------------------------------
# Generated ToDoc implementations


impl ToDoc[ModuleTcEnv]:
    toDoc(self: ModuleTcEnv) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("_traitEnv =")
                + Doc.nested(4, Doc.break_(1) + self._traitEnv.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_cons =")
                + Doc.nested(4, Doc.break_(1) + self._cons.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_topSchemes =")
                + Doc.nested(4, Doc.break_(1) + self._topSchemes.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("_assocFnSchemes =")
                + Doc.nested(4, Doc.break_(1) + self._assocFnSchemes.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)

        # args += Doc.grouped(
        #     Doc.str("_methodSchemes =")
        #         + Doc.nested(4, Doc.break_(1) + self._methodSchemes.toDoc()),
        # )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("ModuleTcEnv") + Doc.char('(') + args)


impl[ToDoc[idx], ToDoc[info]] ToDoc[TcItem[idx, info]]:
    toDoc(self: TcItem[idx, info]) Doc:
        let args = Doc.break_(0)
        args += Doc.grouped(
            Doc.str("idx =") + Doc.nested(4, Doc.break_(1) + self.idx.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("info =") + Doc.nested(4, Doc.break_(1) + self.info.toDoc()),
        )
        args += Doc.char(',') + Doc.break_(1)
        args += Doc.grouped(
            Doc.str("imports =")
                + Doc.nested(4, Doc.break_(1) + self.imports.toDoc()),
        )
        args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
        Doc.grouped(Doc.str("TcItem") + Doc.char('(') + args)
