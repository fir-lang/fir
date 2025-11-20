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
            TopDecl.Type(decl): addMissingTypeParamsType(decl, tokens)

            TopDecl.Fun(decl):
                addMissingTypeParamsFun(decl.sig, OrderedMap.empty(), tokens)

            TopDecl.Import(decl): ()

            TopDecl.Trait(decl): addMissingTypeParamsTrait(decl, tokens)

            TopDecl.Impl(decl): addMissingTypeParamsImpl(decl, tokens)


addMissingTypeParamsType(ty: TypeDecl, tokens: Array[Token]):
    # TODO
    ()


## `tvs` are the variables bound in the enclosing `trait` or `impl` context.
##
## When checking a `trait`, the updated kinds in `tvs` will be used as the kinds
## `trait` type parameters.
##
## When checking an `impl`, the kinds of type parameters in `tvs` should all be
## specified before calling this function.
addMissingTypeParamsFun(
    sig: FunSig,
    tvs: OrderedMap[Str, Option[Kind]],
    tokens: Array[Token],
):
    let boundVars: HashSet[Str] = HashSet.fromIter(tvs.keys())

    if sig.context is Option.Some(context):
        for pred: Type in context.preds.iter():
            collectTvs(pred, tvs, tokens)

    # TODO
    ()


addMissingTypeParamsTrait(trait_: TraitDecl, tokens: Array[Token]):
    # TODO
    ()


addMissingTypeParamsImpl(impl_: ImplDecl, tokens: Array[Token]):
    # TODO
    ()


collectTvs(ty: Type, tvs: OrderedMap[Str, Option[Kind]], tokens: Array[Token]):
    match ty:
        Type.Named(namedTy): collectNamedTyTvs(namedTy, tvs, tokens)

        # TODO
        Type.Var(var_): ()

        # TODO
        Type.Record(RecordType(fields, extension, ..)): ()

        # TODO
        Type.Variant(VariantType(alts, extension, ..)): ()

        # TODO
        Type.Fn_(FnType(args, ret, exceptions, ..)): ()


collectNamedTyTvs(
    namedTy: NamedType,
    tvs: OrderedMap[Str, Option[Kind]],
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
            collectTvs(arg, tvs, tokens)


# ------------------------------------------------------------------------------


type InsertionOrder[t](
    insertionOrder: U32,
    thing: t,
)


type OrderedMap[k, v](
    _map: HashMap[k, InsertionOrder[v]],
)


OrderedMap.empty() OrderedMap[k, v]:
    OrderedMap(_map = HashMap.empty())


OrderedMap.keys(self: OrderedMap[k, v]) Map[HashMapIter[k, InsertionOrder[v]], HashMapEntry[k, InsertionOrder[v]], k, exn] / exn:
    self._map.keys()


OrderedMap.insert[Hash[k], Eq[k]](self: OrderedMap[k, v], key: k, value: v) Option[v]:
    let insertionOrder = self._map.len()
    let value = InsertionOrder(insertionOrder, thing = value)
    self._map.insert(key, value).map(|v|: v.thing)


OrderedMap.orderedEntries(self: OrderedMap[k, v]) Vec[HashMapEntry[k, v]]:
    let vec: Vec[HashMapEntry[k, InsertionOrder[v]]] = Vec.fromIter(
        self._map.iter(),
    )

    vec.sortBy(
        |v1: HashMapEntry[k, InsertionOrder[v]], v2: HashMapEntry[k, InsertionOrder[v]]| Ordering:
            v1.value.insertionOrder.cmp(v2.value.insertionOrder),
    )

    Vec.fromIter(
        vec.iter().map(
            |v: HashMapEntry[k, InsertionOrder[v]]| HashMapEntry[k, v]:
                HashMapEntry(key = v.key, value = v.value.thing),
        ),
    )
