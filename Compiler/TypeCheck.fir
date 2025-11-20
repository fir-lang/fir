# Import all modules temporarily to type check all.
import [
    Compiler/Program,
    Compiler/ScopeMap,
    Compiler/TypeCheck/Convert,
    Compiler/TypeCheck/Error,
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
            prepModuleTyEnv(pgm, modIdx)

    # All modules have access to all `TyCon`s that they need, add `TyCon`
    # details.
    for modIdx: U32 in range(u32(0), pgm._modules.len()):
        initModTyConDetails(pgm, ModuleIdx(_idx = modIdx))


prepModuleTyEnv(pgm: Program, modIdx: ModuleIdx):
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
                            tyParams = Vec.empty(),
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
                            tyParams = Vec.empty(),
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


initModTyConDetails(pgm: Program, modIdx: ModuleIdx) / TypeError:
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
                            name = traitDecl.typeParams.get(i),
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

            let funPreds: Vec[Pred] = match method.sig.context:
                Option.Some(context):
                    convertAndBindContext(
                        mod,
                        varMap,
                        context.typeParams,
                        context.preds,
                        TyVarConversion.ToQVar,
                    )
                Option.None: Vec.empty()

            let argTys: Vec[Ty] = Vec.fromIter(
                method.sig.params.iter().map(
                    |param: FunArg| Ty:
                        # TODO: loc
                        convertAstTy(
                            mod,
                            varMap,
                            param.ty.unwrap(),
                            Loc(file = "", line = 0, col = 0),
                        ),
                ),
            )

            # TODO

            varMap.exitScope()
            assert(varMap.lenScopes() == 1)

        tyCon.info.details = TyConDetails.Trait(TraitDetails(methods))


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


type Import(
    ## Name the item imported as. E.g. in `import [Foo/Bar as Baz]` this will be
    ## `Baz`.
    name: Id,

    ## The path the item was imported from. In the example above: `Foo/Bar`.
    ##
    ## The same item can be imported via different paths.
    importLoc: Vec[Id],
)


ModuleTcEnv.empty() ModuleTcEnv:
    ModuleTcEnv(
        _traitEnv = TraitEnv.empty(),
        _cons = HashMap.empty(),
        _topSchemes = HashMap.empty(),
        _assocFnSchemes = HashMap.empty(),
        _methodSchemes = HashMap.empty(),
    )


## Add imported things from an imported SCC to the current module.
ModuleTcEnv.addImportedThings(self, importedEnv: ModuleTcEnv):
    # TODO: Panics below should be errors.
    # TODO: The code below is not right: the same type or term can be imported
    # via different modules. So importing something multiple times is not a
    # problem as long as we import the same thing.

    # Add type constructors.
    for con: HashMapEntry[Str, TcItem[TyDefIdx, TyCon]] in
            importedEnv._cons.iter():
        let old = self._cons.insert(con.key, con.value)
        if old is Option.Some(_):
            # TODO: Handle importing the same type. (compare TyIds, update
            # import list)
            panic("Type `con.key` imported multiple times")

    # Add traits.
    # TODO: TraitEnv doesn't let you rename traits. Needs refactoring.

    # Add top-level functions.
    for top: HashMapEntry[Str, TcItem[VarDefIdx, Scheme]] in
            importedEnv._topSchemes.iter():
        let old = self._topSchemes.insert(top.key, top.value)
        if old is Option.Some(_):
            panic("Top-level function `top.key` imported multiple times")

    # Add associated functions.
    # TODO: We may import a type with another name, the associated function
    # should be added to the right type when we do that.
    for assoc: HashMapEntry[Str, HashMap[Str, TcItem[VarDefIdx, Scheme]]] in
            importedEnv._assocFnSchemes.iter():
        let tyMap = match self._assocFnSchemes.get(assoc.key):
            Option.Some(tyMap): tyMap
            Option.None:
                let tyMap = HashMap.withCapacity(10)
                self._assocFnSchemes.insert(assoc.key, tyMap)
                tyMap

        for fun: HashMapEntry[Str, TcItem[VarDefIdx, Scheme]] in
                assoc.value.iter():
            let old = tyMap.insert(fun.key, fun.value)
            if old is Option.Some(_):
                panic(
                    "Associated function `assoc.key`.`fun.key` imported multiple times.",
                )


# Add methods.
# TODO


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
