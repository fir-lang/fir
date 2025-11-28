## Defines the program-level state: package and module database.


import [
    Compiler/Ast,
    Compiler/Defs,
    Compiler/Error,
    Compiler/Grammar,
    Compiler/Module,
    Compiler/Scanner,
    Compiler/TypeCheck,
]


type Program(
    ## Indexed by `ModuleIdx`.
    _modules: Vec[Module],

    ## Strongly connected graphs of modules. Indexed by SCC indices.
    ##
    ## Initialized by `prepModuleEnvs`.
    _depGraph: Option[Vec[HashSet[ModuleIdx]]],
)


Program.new() Program:
    Program(_modules = Vec.empty(), _depGraph = Option.None,)


Program.tyCon(self, tyIdx: TyDefIdx) TyCon:
    let mod = self._modules.get(tyIdx._mod._idx)
    mod.tyCon(tyIdx)


## Load a module, or return it from the cache if it's already loaded.
##
## Follows imports in the module to transitively import all referred modules.
##
## This only parses the loaded modules. The generated `Module` won't have name
## resolving and type checking environments.
Program.loadCachedModule(self, path: Vec[Str]) ModuleIdx:
    let firPreludePath = Vec.["Fir", "Prelude"]

    for module: Module in self._modules.iter():
        if module._path == path:
            return module._idx

    print("Loading path: `path`...")

    let filePath = _modulePathToFilePath(path)
    let parsedModule = _parseFile(filePath)
    addMissingTypeParams(parsedModule.decls, parsedModule.tokens)
    let moduleDecls = parsedModule.decls
    let tokens = parsedModule.tokens

    # Add the module to the program first to handle recursive imports.
    let moduleIdx = ModuleIdx(_idx = self._modules.len())

    let funItems: HashMap[Str, FunDecl] = HashMap.withCapacity(100)
    let assocItems: HashMap[Str, HashMap[Str, FunDecl]] = HashMap.withCapacity(
        10,
    )
    let tyItems: HashMap[Str, TypeDecl] = HashMap.withCapacity(100)
    let traitItems: HashMap[Str, TraitDecl] = HashMap.withCapacity(10)
    let impls: Vec[ImplDecl] = Vec.empty()
    let imports: Vec[Vec[Str]] = Vec.empty()

    # Implicitly import `Fir/Prelude` in all modules.
    # TODO: Implement flag `--no-prelude`.
    # TODO: What happens if the module explicitly imports `Fir/Prelude`?
    if path != firPreludePath:
        imports.push(Vec.["Fir", "Prelude"])

    for decl: TopDecl in moduleDecls.iter():
        match decl:
            TopDecl.Type(typeDecl):
                let name = tokens.get(typeDecl.name.token.idx).text
                let old = tyItems.insert(name, typeDecl)
                if old is Option.Some(_):
                    panic("Type `name` defined multiple times in `filePath`")

            TopDecl.Fun(funDecl):
                match funDecl.parentTy:
                    Option.Some(parentTy):
                        let parentTyName = tokens.get(parentTy.token.idx).text
                        let assocFunMap = match assocItems.get(parentTyName):
                            Option.None:
                                let map = HashMap.withCapacity(10)
                                assocItems.insert(parentTyName, map)
                                map
                            Option.Some(map): map
                        let funName = tokens.get(funDecl.name.token.idx).text
                        let old = assocFunMap.insert(funName, funDecl)
                        if old is Option.Some(_):
                            panic(
                                "Associated function `parentTyName`.`funName` defined multipe times in `filePath`",
                            )

                    Option.None:
                        let funName = tokens.get(funDecl.name.token.idx).text
                        let old = funItems.insert(funName, funDecl)
                        if old is Option.Some(_):
                            panic(
                                "Function `funName` defined multipe times in `filePath`",
                            )

            TopDecl.Trait(traitDecl):
                let traitName = tokens.get(traitDecl.name.token.idx).text
                let old = traitItems.insert(traitName, traitDecl)
                if old is Option.Some(_):
                    panic(
                        "Trait `traitName` defined multiple times in `filePath`",
                    )

            TopDecl.Impl(implDecl): impls.push(implDecl)

            TopDecl.Import(importDecl):
                for path: Vec[Id] in importDecl.paths.iter():
                    imports.push(
                        Vec.fromIter(
                            path.iter().map(
                                \(id: Id) Str: tokens.get(id.token.idx).text,
                            ),
                        ),
                    )

    let module = Module(
        _package = _defaultPackage(),
        _filePath = filePath,
        _path = path,
        _idx = moduleIdx,
        _funItems = funItems,
        _assocItems = assocItems,
        _tyItems = tyItems,
        _traitItems = traitItems,
        _impls = impls,
        _imports = Vec.withCapacity(imports.len()),
        _tokens = tokens,
        _termEnv = HashMap.withCapacity(100),
        _assocTermEnv = HashMap.withCapacity(10),
        _tyEnv = HashMap.withCapacity(100),
        _tcEnv = Option.None,
        _sccIdx = Option.None,
    )

    self._modules.push(module)

    for import_: Vec[Str] in imports.iter():
        let importedModuleIdx = self.loadCachedModule(import_)
        module._imports.push(importedModuleIdx)

    moduleIdx


# ------------------------------------------------------------------------------


_parseFile(path: Str) (decls: Vec[TopDecl], tokens: Array[Token]):
    let fileContents = readFileUtf8(path)

    let (tokens, error) = tokenize(path, fileContents)
    if error is Option.Some(error):
        panic("`path`:`error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    # Explicitly close the variant with `row[]`. (#49)
    let tokens = match try(\(): scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("`path`:`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens

    match try(\(): module(ParserState.new(tokens))):
        Result.Err(cursor):
            match tokens.getOpt(cursor):
                Option.None: panic("`path`: unexpected end of input")
                Option.Some(token):
                    panic(
                        "`path`:`token.line + 1`:`token.col + 1`: unexpected token `token`",
                    )
        Result.Ok(mod): (decls = mod, tokens = tokens.takeArray())


_modulePathToFilePath(path: Vec[Str]) Str:
    let filePath = StrBuf.withCapacity(80)

    for i: U32 in range(u32(0), path.len()):
        if i != 0:
            filePath.push('/')
        filePath.pushStr(path.get(i))
        i += 1

    filePath.pushStr(".fir")
    filePath.toStr()


_defaultPackage() PackageUri:
    PackageUri(_uri = "pgk:default")
