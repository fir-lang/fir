#|
For now this is just a port of the interpreter's purely syntactic kind inference
implementation:

- `RecRow` and `VarRow` trait predicates make the type arguments record and
  variant rows. These traits are defined in the standard library.

- `recRow` and `varRow` prefixes in type variables make the type variables
  record and variant rows.

(I don't remember why we needed both, just the prefixes should be enough to
specify kinds of all type parameters.)

Because this pass is purely syntactic, we run it as first thing after parsing
and then don't worry about missing type parameter kinds afterwards.

This also adds missing type parameters to function declarations, e.g.

    id(x: t) t: x
    ==>
    id[t](x: t) t: x
|#


import [Compiler/Ast]


addMissingTypeParams(mod: Vec[TopDecl], tokens: Array[Token]):
    for decl: TopDecl in mod.iter():
        match decl:
            TopDecl.Type(decl): _addMissingTypeParamsType(decl, tokens)

            TopDecl.Fun(decl):
                _addMissingTypeParamsFun(
                    decl.sig, OrderedHashMap.empty(), tokens,
                )

            TopDecl.Import(decl): ()

            TopDecl.Trait(decl): _addMissingTypeParamsTrait(decl, tokens)

            TopDecl.Impl(decl): _addMissingTypeParamsImpl(decl, tokens)


_addMissingTypeParamsType(ty: TypeDecl, tokens: Array[Token]):
    let kinds: Vec[Kind] = Vec.withCapacity(ty.typeParams.len())

    for tyParam: DeclTypeParam in ty.typeParams.iter():
        let kind = _convertKind(tyParam.kind, tokens).unwrapOr(Kind.Star)
        kinds.push(kind)

    ty.typeParamKinds = kinds


## `tvs` are the variables bound in the enclosing `trait` or `impl` context.
##
## When checking a `trait`, the updated kinds in `tvs` will be used as the kinds
## `trait` type parameters.
##
## When checking an `impl`, the kinds of type parameters in `tvs` should all be
## specified before calling this function.
_addMissingTypeParamsFun(
    sig: FunSig,
    tvs: OrderedHashMap[Str, Option[Kind]],
    tokens: Array[Token],
):
    let boundVars: HashSet[Str] = HashSet.fromIter(tvs.keys())

    if sig.context is Option.Some(context):
        for pred: Pred_ in context.preds.iter():
            match pred:
                Pred_.Kind(name = kindVar, kind):
                    let varStr = tokens.get(kindVar.token.idx).text
                    let kind = _convertKind(kind, tokens)
                    tvs.insert(varStr, kind)
                Pred_.App(NamedType(name = _, args)):
                    for arg: Type in args.unwrap().args.iter():
                        _collectTvs(arg, tvs, tokens)
                Pred_.AssocTyEq(ty = NamedType(name = _, args), assocTy = _, eq):
                    for arg: Type in args.unwrap().args.iter():
                        _collectTvs(arg, tvs, tokens)
                    _collectTvs(eq, tvs, tokens)

    match sig.self_:
        SelfParam.No | SelfParam.Implicit: ()
        SelfParam.Explicit(ty): _collectTvs(ty, tvs, tokens)

    for arg: FunArg in sig.params.iter():
        if arg.ty is Option.Some(ty):
            _collectTvs(ty, tvs, tokens)

    if sig.exceptions is Option.Some(ty):
        _collectTvs(ty, tvs, tokens)

    if sig.returnTy is Option.Some(ty):
        _collectTvs(ty, tvs, tokens)

    for entry: HashMapEntry[Str, Option[Kind]] in tvs.orderedEntries().iter():
        if boundVars.contains(entry.key):
            continue

        let fvKind = entry.val.unwrapOr(Kind.Star)
        sig.typeParams.push(
            TypeParam(name = LocalId(name = entry.key), kind = fvKind),
        )


_addMissingTypeParamsTrait(trait_: TraitDecl, tokens: Array[Token]):
    assert(trait_.typeParamKinds.isEmpty())

    let traitContextVarKinds: OrderedHashMap[Str, Option[Kind]] = OrderedHashMap
        .empty()
    let traitContextVars: HashSet[Str] = HashSet.empty()

    for param: DeclTypeParam in trait_.typeParams.iter():
        let paramStr = tokens.get(param.name.token.idx).text
        let kind = _convertKind(param.kind, tokens)
        traitContextVarKinds.insert(paramStr, kind)
        traitContextVars.insert(paramStr)

    for item: TraitDeclItem in trait_.items.iter():
        let fun = match item:
            TraitDeclItem.Type(..): continue
            TraitDeclItem.Fun(fun): fun

        # Update trait context variable kinds. This also adds function context
        # variables, which we remove below.
        _addMissingTypeParamsFun(fun.sig, traitContextVarKinds, tokens)

        # Drop function context variables added above.
        let keysToDrop: Vec[Str] = Vec.fromIter(
            traitContextVarKinds.keys().filter(
                \(key: Str) Bool: not traitContextVars.contains(key),
            ),
        )

        for key: Str in keysToDrop.iter():
            traitContextVarKinds.remove(key)

    let traitContextVarKinds = traitContextVarKinds.orderedEntries()
    trait_.typeParamKinds = Vec.fromIter(
        traitContextVarKinds.iter().map(
            \(entry: HashMapEntry[Str, Option[Kind]]) Kind:
                entry.val.unwrapOr(Kind.Star),
        ),
    )


_addMissingTypeParamsImpl(impl_: ImplDecl, tokens: Array[Token]):
    assert(impl_.typeParams.isEmpty())

    let implContextVarKinds: OrderedHashMap[Str, Option[Kind]] = OrderedHashMap
        .empty()

    if impl_.context is Option.Some(context):
        for pred: Pred_ in context.preds.iter():
            match pred:
                Pred_.Kind(name = kindVar, kind):
                    let varStr = tokens.get(kindVar.token.idx).text
                    let kind = _convertKind(kind, tokens)
                    implContextVarKinds.insert(varStr, kind)
                Pred_.App(NamedType(name = _, args)):
                    for arg: Type in args.unwrap().args.iter():
                        _collectTvs(arg, implContextVarKinds, tokens)
                Pred_.AssocTyEq(ty = NamedType(name = _, args), assocTy = _, eq):
                    for arg: Type in args.unwrap().args.iter():
                        _collectTvs(arg, implContextVarKinds, tokens)
                    _collectTvs(eq, implContextVarKinds, tokens)

    for ty: Type in impl_.tys.iter():
        _collectTvs(ty, implContextVarKinds, tokens)

    # This is a set but we use the map type because I'm lazy.
    let implContextVars: OrderedHashMap[Str, ()] = OrderedHashMap.empty()

    for var_: Str in implContextVarKinds.keys():
        implContextVars.insert(var_, ())

    for item: ImplDeclItem in impl_.items.iter():
        let fun = match item:
            ImplDeclItem.Type(..): continue
            ImplDeclItem.Fun(fun): fun

        # Same as the loop in in the trait decl case above.
        _addMissingTypeParamsFun(fun.sig, implContextVarKinds, tokens)

        let keysToDrop: Vec[Str] = Vec.fromIter(
            implContextVarKinds.keys().filter(
                \(key: Str) Bool: not implContextVars.containsKey(key),
            ),
        )

        for key: Str in keysToDrop.iter():
            implContextVarKinds.remove(key)

    for var_: HashMapEntry[Str, ()] in implContextVars.orderedEntries().iter():
        impl_.typeParams.push(
            TypeParam(
                name = LocalId(name = var_.key),
                kind =
                    implContextVarKinds.get(var_.key).unwrap().unwrapOr(
                        Kind.Star,
                    ),
            ),
        )


## Convert an optional AST kind annotation to an internal Kind.
##
## Returns `None` when no annotation, otherwise expects `Row[Rec]` or
## `Row[Var]`.
_convertKind(kind: Option[Type], tokens: Array[Token]) Option[Kind]:
    match kind:
        Option.None: Option.None
        Option.Some(Type.Named(NamedType(name, args))):
            if tokens.get(name.token.idx).text != "Row":
                panic("Kind annotation must be Row[Rec] or Row[Var]")
            let args = args.unwrap().args
            if args.len() != 1:
                panic("Kind annotation must be Row[Rec] or Row[Var]")
            match args.get(0):
                Type.Named(NamedType(name = argName, args = _)):
                    let argNameStr = tokens.get(argName.token.idx).text
                    if argNameStr == "Rec":
                        Option.Some(Kind.Row(RecordOrVariant.Record))
                    elif argNameStr == "Var":
                        Option.Some(Kind.Row(RecordOrVariant.Variant))
                    else:
                        panic("Kind annotation must be Row[Rec] or Row[Var]")
                _: panic("Kind annotation must be Row[Rec] or Row[Var]")
        _: panic("Kind annotation must be Row[Rec] or Row[Var]")


## Collect type variables in `ty` in `tvs`.
##
## If a type variable is an argument to the special marker traits `RecRow` or
## `VarRow`, or the variable is used in a row position, the kind of the type
## variable is added as a record or variant row in `tvs`. Otherwise we don't
## specify the kind of the variable so that we can update it as record or
## variant row when we see one of the marker traits later, or default the kind
## as `*` if not.
_collectTvs(
    ty: Type,
    tvs: OrderedHashMap[Str, Option[Kind]],
    tokens: Array[Token],
):
    match ty:
        Type.Named(namedTy): _collectNamedTyTvs(namedTy, tvs, tokens)

        Type.Var(var_):
            let varName = tokens.get(var_.token.idx).text
            if not tvs.containsKey(varName):
                tvs.insert(varName, Option.None)
            ()

        Type.Record(RecordType(fields, extension, ..)):
            for field: Named[Type] in fields.iter():
                _collectTvs(field.node, tvs, tokens)

            if extension is Option.Some(ext):
                match ext:
                    Type.Var(var_):
                        let extName = tokens.get(var_.token.idx).text
                        if tvs.insert(
                                extName,
                                Option.Some(Kind.Row(RecordOrVariant.Record)),
                            )
                                is Option.Some(Option.Some(old))
                                and old != Kind.Row(RecordOrVariant.Record):
                            panic("Conflicting kind of type variable")
                    other: _collectTvs(other, tvs, tokens)

        Type.Variant(VariantType(alts, extension, ..)):
            for alt: NamedType in alts.iter():
                _collectNamedTyTvs(alt, tvs, tokens)

            if extension is Option.Some(ext):
                match ext:
                    Type.Var(var_):
                        let extName = tokens.get(var_.token.idx).text
                        if tvs.insert(
                                extName,
                                Option.Some(Kind.Row(RecordOrVariant.Variant)),
                            )
                                is Option.Some(Option.Some(old))
                                and old != Kind.Row(RecordOrVariant.Variant):
                            panic("Conflicting kind of type variable")
                    other: _collectTvs(other, tvs, tokens)

        Type.Fn_(FnType(args, ret, exceptions, ..)):
            for arg: Type in args.iter():
                _collectTvs(arg, tvs, tokens)

            if ret is Option.Some(ret):
                _collectTvs(ret, tvs, tokens)

            if exceptions is Option.Some(exn):
                _collectTvs(exn, tvs, tokens)

        Type.AssocTySelect(AssocTySelectType(ty, assocTy = _)):
            _collectTvs(ty, tvs, tokens)


_collectNamedTyTvs(
    namedTy: NamedType,
    tvs: OrderedHashMap[Str, Option[Kind]],
    tokens: Array[Token],
):
    if namedTy.args is Option.Some(args):
        for arg: Type in args.args.iter():
            _collectTvs(arg, tvs, tokens)


# ------------------------------------------------------------------------------


type InsertionOrder[t](
    insertionOrder: U32,
    thing: t,
)


## This map allows iterating the hash map elements in insertion order.
##
## It would probably be more efficient to maintain a linked list of elements
## separately from the wrapped `HashMap`. It shouldn't matter too much for this
## code as the maps keep type parameter in traits, impls, and functions, so
## they're always very small.
type OrderedHashMap[k, v](
    _map: HashMap[k, InsertionOrder[v]],
)


OrderedHashMap.empty() OrderedHashMap[k, v]:
    OrderedHashMap(_map = HashMap.empty())


OrderedHashMap.keys(self: OrderedHashMap[k, v]) Map[HashMapIter[k, InsertionOrder[v]], HashMapEntry[k, InsertionOrder[v]], k, exn] / exn:
    self._map.keys()


OrderedHashMap.containsKey[Hash[k], Eq[k]](self: OrderedHashMap[k, v], key: k) Bool:
    self._map.containsKey(key)


OrderedHashMap.get[Hash[k], Eq[k]](self: OrderedHashMap[k, v], key: k) Option[v]:
    self._map.get(key).map(\(v: InsertionOrder[v]) v: v.thing)


OrderedHashMap.insert[Hash[k], Eq[k]](
    self: OrderedHashMap[k, v],
    key: k,
    val: v,
) Option[v]:
    let insertionOrder = self._map.len()
    let val = InsertionOrder(insertionOrder, thing = val)
    self._map.insert(key, val).map(\(v): v.thing)


OrderedHashMap.remove[Hash[k], Eq[k]](self: OrderedHashMap[k, v], key: k) Option[v]:
    let insertionOrder = self._map.len()
    self._map.remove(key).map(\(v): v.thing)


OrderedHashMap.orderedEntries(self: OrderedHashMap[k, v]) Vec[HashMapEntry[k, v]]:
    let vec: Vec[HashMapEntry[k, InsertionOrder[v]]] = Vec.fromIter(
        self._map.iter(),
    )

    vec.sortBy(
        \(v1: HashMapEntry[k, InsertionOrder[v]], v2: HashMapEntry[k, InsertionOrder[v]]) Ordering:
            v1.val.insertionOrder.cmp(v2.val.insertionOrder),
    )

    Vec.fromIter(
        vec.iter().map(
            \(v: HashMapEntry[k, InsertionOrder[v]]) HashMapEntry[k, v]:
                HashMapEntry(key = v.key, val = v.val.thing),
        ),
    )


impl[Clone[k], Clone[v]] Clone[OrderedHashMap[k, v]]:
    clone(self: OrderedHashMap[k, v]) OrderedHashMap[k, v]:
        OrderedHashMap(_map = self._map.clone())


impl[Clone[t]] Clone[InsertionOrder[t]]:
    clone(self: InsertionOrder[t]) InsertionOrder[t]:
        InsertionOrder(
            insertionOrder = self.insertionOrder, thing = self.thing.clone(),
        )
