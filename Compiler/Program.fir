## Defines the program-level state: package and module database.


import [
    Compiler/Ast,
    Compiler/Defs,
    Compiler/Error,
    Compiler/Grammar,
    Compiler/Scanner,
]


type Program(
    _modules: Vec[Module],
)


## Load a module, or return it from the cache if it's already loaded.
##
## Follows imports in the module to transitively import all referred modules.
Program.loadCachedModule(self, path: Vec[Str]) ModuleIdx:
    for module: Module in self._modules.iter():
        if module._path == path:
            return module._idx

    let filePath = _modulePathToFilePath(path)
    let parsedModule = _parseFile(filePath)
    let moduleDecls = parsedModule.decls
    let tokens = parsedModule.tokens

    # Add the module to the program first to handle recursive imports.
    let moduleIdx = ModuleIdx(_idx = self._modules.len())

    let varItems: Vec[VarDef] = Vec.empty()
    let tyItems: Vec[TyDef] = Vec.empty()
    let traitItems: Vec[TraitDef] = Vec.empty()
    let impls: Vec[ImplDecl] = Vec.empty()
    let imports: Vec[Vec[Str]] = Vec.empty()
    for decl: TopDecl in moduleDecls.iter():
        match decl:
            TopDecl.Type(typeDecl):
                let idx = TyDefIdx_(_mod = moduleIdx, _tyIdx = tyItems.len())
                tyItems.push(TyDef(_ast = typeDecl, _idx = idx))

            TopDecl.Fun(funDecl):
                let idx = TopVarDefIdx(_mod = moduleIdx, _idx = varItems.len())
                varItems.push(VarDef(_ast = funDecl, _idx = idx))

            TopDecl.Trait(traitDecl):
                let idx = TraitDefIdx(
                    _mod = moduleIdx,
                    _traitIdx = traitItems.len(),
                )
                traitItems.push(TraitDef(_ast = traitDecl, _idx = idx))

            TopDecl.Impl(implDecl): impls.push(implDecl)

            TopDecl.Import(importDecl):
                for path: Vec[Id] in importDecl.paths.iter():
                    imports.push(
                        path.iter().map(
                            |id: Id| Str: tokens.get(id.token.idx).text,
                        ).toVec(),
                    )

    let module = Module(
        _package = _defaultPackage(),
        _path = path,
        _idx = moduleIdx,
        _varItems = varItems,
        _tyItems = tyItems,
        _traitItems = traitItems,
        _impls = impls,
        _imports = Vec.withCapacity(imports.len()),
        _tokens = tokens,
    )

    self._modules.push(module)

    for import_: Vec[Str] in imports.iter():
        let importedModuleIdx = self.loadCachedModule(import_)
        module._imports.push(importedModuleIdx)

    moduleIdx


_parseFile(path: Str) (decls: Vec[TopDecl], tokens: Array[Token]):
    let fileContents = readFileUtf8(path)

    let (tokens, error) = tokenize(path, fileContents)
    if error is Option.Some(error):
        panic("`path`:`error.loc.line + 1`:`error.loc.col + 1`: `error.msg`")

    # Explicitly close the variant with `row[]`. (#49)
    let tokens = match try(||: scan[row[]](tokens)):
        Result.Err(~ScannerError(line, col, msg)):
            panic("`path`:`line + 1`:`col + 1`: `msg`")
        Result.Ok(tokens): tokens

    match try(||: module(ParserState.new(tokens))):
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
