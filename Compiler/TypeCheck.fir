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
    Compiler/TypeCheck/TyMap,
    Compiler/TypeCheck/Unification,
]


prepTcEnvs(pgm: Program):
    ()


prepSccTyEnv(pgm: Program, sccIdx: U32) ModuleTcEnv:
    if pgm._sccTyEnvs.get(sccIdx) is Option.Some(env):
        return env

    let moduleDeps: HashSet[ModuleIdx] = pgm._depGraph.unwrap().get(sccIdx)

    let sccDeps: HashSet[U32] = HashSet.fromIter(
        moduleDeps.iter().map(
            |modIdx: ModuleIdx|: pgm._modules.get(modIdx._idx)._sccIdx.unwrap(),
        ),
    )

    let sccModules = pgm._depGraph.unwrap().get(sccIdx)

    # Pick one of the modules from the SCC. It doesn't matter which one as all
    # modules in the SCC will have the same type checking environment.
    let selfModuleIdx: ModuleIdx = sccModules.iter().next().unwrap()
    let selfModule = pgm._modules.get(selfModuleIdx._idx)

    # Initialize the env for the current SCC with the imported things (both
    # types and terms).
    let selfTcEnv = ModuleTcEnv.empty()

    for depScc: U32 in sccDeps.iter():
        let depSccEnv = prepSccTyEnv(pgm, depScc)
        selfTcEnv.addImportedThings(depSccEnv)

    # TODO: Add things defined in the current SCC.

    selfTcEnv


# ------------------------------------------------------------------------------
# Module type checking environment


## The module environment holds type constructors, traits (with impls), and
## associated and top-level functions available in the module.
type ModuleTcEnv(
    ## The traits, with impls.
    _traitEnv: TraitEnv,

    ## Type constructors.
    _cons: HashMap[Str, TyCon],

    ## Top-level function schemes.
    _topSchemes: HashMap[Str, Scheme],

    ## Associated function schemes.
    _assocFnSchemes: HashMap[Str, HashMap[Str, Scheme]],

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


type Imported[def](
    def: def,
    imports: Vec[Import],
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
    for con: HashMapEntry[Str, TyCon] in importedEnv._cons.iter():
        let old = self._cons.insert(con.key, con.value)
        if old is Option.Some(_):
            panic("Type `con.key` imported multiple times")

    # Add traits.
    # TODO: TraitEnv doesn't let you rename traits. Needs refactoring.

    # Add top-level functions.
    for top: HashMapEntry[Str, Scheme] in importedEnv._topSchemes.iter():
        let old = self._topSchemes.insert(top.key, top.value)
        if old is Option.Some(_):
            panic("Top-level function `top.key` imported multiple times")

    # Add associated functions.
    # TODO: We may import a type with another name, the associated function
    # should be added to the right type when we do that.
    for assoc: HashMapEntry[Str, HashMap[Str, Scheme]] in
            importedEnv._assocFnSchemes.iter():
        let tyMap = match self._assocFnSchemes.get(assoc.key):
            Option.Some(tyMap): tyMap
            Option.None:
                let tyMap = HashMap.withCapacity(10)
                self._assocFnSchemes.insert(assoc.key, tyMap)
                tyMap

        for fun: HashMapEntry[Str, Scheme] in assoc.value.iter():
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
