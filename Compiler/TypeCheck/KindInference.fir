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


addMissingTypeParams(mod: Vec[TopDecl], tokens: Vec[Token]):
    for decl: TopDecl in mod.iter():
        match decl:
            TopDecl.Type(decl): addMissingTypeParamsType(decl, tokens)

            TopDecl.Fun(decl):
                addMissingTypeParamsFun(decl.sig, OrderedMap.empty(), tokens)

            TopDecl.Import(decl): ()

            TopDecl.Trait(decl): addMissingTypeParamsTrait(decl, tokens)

            TopDecl.Impl(decl): addMissingTypeParamsImpl(decl, tokens)


addMissingTypeParamsType(ty: TypeDecl, tokens: Vec[Token]):
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
    tvs: OrderedMap[Str, Kind],
    tokens: Vec[Token],
):
    let boundVars: HashSet[Str] = HashSet.fromIter(tvs.keys())

    if sig.context is Option.Some(context):
        # TODO: typeParams should be moved out of `Context` as `Context` may not
        # be available when the function has type parameters.
        ()

    # TODO
    ()


addMissingTypeParamsTrait(trait_: TraitDecl, tokens: Vec[Token]):
    # TODO
    ()


addMissingTypeParamsImpl(impl_: ImplDecl, tokens: Vec[Token]):
    # TODO
    ()


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
