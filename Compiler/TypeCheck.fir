# Import all modules temporarily to type check all.
import [
    Compiler/Program,
    Compiler/ScopeMap,
    Compiler/TypeCheck/Convert,
    Compiler/TypeCheck/Error,
    Compiler/TypeCheck/KindInference,
    Compiler/TypeCheck/Normalization,
    Compiler/TypeCheck/RowUtils,
    Compiler/TypeCheck/TraitEnv,
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/TyCon,
    Compiler/TypeCheck/Unification,
]


prepTcEnvs(pgm: Program) / TypeError:
    # Prep envs in dependency order: from imported SCCs to importing SCCs.
    # In the future: we probably want to prep SCC envs on demand to allow
    # prepping only the needed envs. I.e. recursively prep envs, cache prepped
    # envs.
    for scc: HashSet[ModuleIdx] in pgm._depGraph.unwrap().iter():
        for modIdx: ModuleIdx in scc.iter():
            prepModuleTyCons(pgm, modIdx)

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


prepModuleTyCons(pgm: Program, modIdx: ModuleIdx):
    if pgm._modules.get(modIdx._idx)._tcEnv is Option.Some(env):
        return

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

    let depGraph = pgm._depGraph.unwrap()

    # SCC index of the current module.
    let sccIdx = pgm._modules.get(modIdx._idx)._sccIdx.unwrap()

    # Modules in the current SCC.
    let sccModules: HashSet[ModuleIdx] = pgm._depGraph.unwrap().get(sccIdx)

    initSccTyCons(pgm, sccModules)


initSccTyCons(pgm: Program, sccModules: HashSet[ModuleIdx]):
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

            if method.sig.exceptions is Option.None:
                # The name we invent for the exception type does not matter as
                # it can't be used in the function body. It's also OK to not
                # bind it in `convertAndBindContext` above for the same reason.
                schemeQVars.push(
                    QVar(id = LocalId(name = "?exn"), kind = Kind.Star),
                )

            for tyParam: TypeParam in method.sig.typeParams.iter():
                schemeQVars.push(QVar(id = tyParam.name, kind = tyParam.kind))

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


addModSchemes(pgm: Program, modIdx: ModuleIdx) / TypeError:
    # TODO
    ()


# ------------------------------------------------------------------------------
# Module type checking environment


## The module environment holds type constructors, traits (with impls), and
## associated and top-level functions available in the module.
type ModuleTcEnv(
    ## The traits, with impls.
    _traitEnv: TraitEnv,

    ## Type constructors.
    _cons: HashMap[Str, TcItem[TyDefIdx, TyCon]],

    ## Top-level function schemes.
    _topSchemes: HashMap[Str, TcItem[VarDefIdx, Scheme]],

    ## Associated function schemes.
    _assocFnSchemes: HashMap[Str, HashMap[Str, TcItem[VarDefIdx, Scheme]]],

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


# ------------------------------------------------------------------------------
# Generated ToDoc implementations


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
