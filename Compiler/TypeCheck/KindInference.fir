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
                    decl.sig,
                    OrderedHashMap.empty(),
                    tokens,
                )

            TopDecl.Import(decl): ()

            TopDecl.Trait(decl): _addMissingTypeParamsTrait(decl, tokens)

            TopDecl.Impl(decl): _addMissingTypeParamsImpl(decl, tokens)


_addMissingTypeParamsType(ty: TypeDecl, tokens: Array[Token]):
    let kinds: Vec[Kind] = Vec.withCapacity(ty.typeParams.len())

    for tyParam: Id in ty.typeParams.iter():
        let tyParamStr = tokens.get(tyParam.token.idx).text
        let kind = if tyParamStr.startsWith("recRow"):
            Kind.Row(RecordOrVariant.Record)
        elif tyParamStr.startsWith("varRow"):
            Kind.Row(RecordOrVariant.Variant)
        else:
            Kind.Star
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
        for pred: Type in context.preds.iter():
            _collectTvs(pred, tvs, tokens)

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

        let fvKind = entry.value.unwrapOr(Kind.Star)
        sig.typeParams.push(
            TypeParam(name = LocalId(name = entry.key), kind = fvKind),
        )


_addMissingTypeParamsTrait(trait_: TraitDecl, tokens: Array[Token]):
    assert(trait_.typeParamKinds.isEmpty())

    let traitContextVarKinds: OrderedHashMap[Str, Option[Kind]] = OrderedHashMap
        .empty()
    let traitContextVars: HashSet[Str] = HashSet.empty()

    for param: Id in trait_.typeParams.iter():
        let paramStr = tokens.get(param.token.idx).text
        traitContextVarKinds.insert(paramStr, Option.None)
        traitContextVars.insert(paramStr)

    for fun: FunDecl in trait_.items.iter():
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
                entry.value.unwrapOr(Kind.Star),
        ),
    )


_addMissingTypeParamsImpl(impl_: ImplDecl, tokens: Array[Token]):
    assert(impl_.typeParams.isEmpty())

    let implContextVarKinds: OrderedHashMap[Str, Option[Kind]] = OrderedHashMap
        .empty()

    if impl_.context is Option.Some(context):
        for pred: Type in context.preds.iter():
            _collectTvs(pred, implContextVarKinds, tokens)

    for ty: Type in impl_.tys.iter():
        _collectTvs(ty, implContextVarKinds, tokens)

    # This is a set but we use the map type because I'm lazy.
    let implContextVars: OrderedHashMap[Str, ()] = OrderedHashMap.empty()

    for var_: Str in implContextVarKinds.keys():
        implContextVars.insert(var_, ())

    for fun: FunDecl in impl_.items.iter():
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
                let extName = tokens.get(ext.token.idx).text
                if tvs.insert(
                        extName,
                        Option.Some(Kind.Row(RecordOrVariant.Record)),
                    )
                        is Option.Some(Option.Some(old))
                        and old != Kind.Row(RecordOrVariant.Record):
                    panic("Conflicting kind of type variable")

        Type.Variant(VariantType(alts, extension, ..)):
            for alt: NamedType in alts.iter():
                _collectNamedTyTvs(alt, tvs, tokens)

            if extension is Option.Some(ext):
                let extName = tokens.get(ext.token.idx).text
                if tvs.insert(
                        extName,
                        Option.Some(Kind.Row(RecordOrVariant.Variant)),
                    )
                        is Option.Some(Option.Some(old))
                        and old != Kind.Row(RecordOrVariant.Variant):
                    panic("Conflicting kind of type variable")

        Type.Fn_(FnType(args, ret, exceptions, ..)):
            for arg: Type in args.iter():
                _collectTvs(arg, tvs, tokens)

            if ret is Option.Some(ret):
                _collectTvs(ret, tvs, tokens)

            if exceptions is Option.Some(exn):
                _collectTvs(exn, tvs, tokens)


_collectNamedTyTvs(
    namedTy: NamedType,
    tvs: OrderedHashMap[Str, Option[Kind]],
    tokens: Array[Token],
):
    if namedTy.name.name == "RecRow" or namedTy.name.name == "VarRow":
        let kind = Kind.Row(
            if namedTy.name.name == "RecRow":
                RecordOrVariant.Record
            else:
                RecordOrVariant.Variant,
        )

        assert(namedTy.args.unwrap().args.len() == 1)

        match namedTy.args.unwrap().args.get(0):
            Type.Var(var_):
                let varName = tokens.get(var_.token.idx).text
                let old = tvs.insert(varName, Option.Some(kind))
                if old is Option.Some(Option.Some(oldKind)) and oldKind != kind:
                    panic("Conflicting kinds")

            other:
                panic("RecRow or RecVar argument needs to be a type variable")

        return

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
    value: v,
) Option[v]:
    let insertionOrder = self._map.len()
    let value = InsertionOrder(insertionOrder, thing = value)
    self._map.insert(key, value).map(\(v): v.thing)


OrderedHashMap.remove[Hash[k], Eq[k]](self: OrderedHashMap[k, v], key: k) Option[v]:
    let insertionOrder = self._map.len()
    self._map.remove(key).map(\(v): v.thing)


OrderedHashMap.orderedEntries(self: OrderedHashMap[k, v]) Vec[HashMapEntry[k, v]]:
    let vec: Vec[HashMapEntry[k, InsertionOrder[v]]] = Vec.fromIter(
        self._map.iter(),
    )

    vec.sortBy(
        \(v1: HashMapEntry[k, InsertionOrder[v]], v2: HashMapEntry[k, InsertionOrder[v]]) Ordering:
            v1.value.insertionOrder.cmp(v2.value.insertionOrder),
    )

    Vec.fromIter(
        vec.iter().map(
            \(v: HashMapEntry[k, InsertionOrder[v]]) HashMapEntry[k, v]:
                HashMapEntry(key = v.key, value = v.value.thing),
        ),
    )


impl[Clone[k], Clone[v]] Clone[OrderedHashMap[k, v]]:
    clone(self: OrderedHashMap[k, v]) OrderedHashMap[k, v]:
        OrderedHashMap(_map = self._map.clone())


impl[Clone[t]] Clone[InsertionOrder[t]]:
    clone(self: InsertionOrder[t]) InsertionOrder[t]:
        InsertionOrder(
            insertionOrder = self.insertionOrder,
            thing = self.thing.clone(),
        )
