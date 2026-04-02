import [
    Compiler/TypeCheck/Ty,
    Compiler/TypeCheck/Unification,
]


#[derive(ToDoc)]
type TraitEnv(
    _map: HashMap[TyId, Vec[TraitImpl]],
)


TraitEnv.empty() TraitEnv:
    TraitEnv(_map = HashMap.empty(),)


# Example: `impl[Iterator[iter, exn], Iterator[iter, exn].Item = a] Iterator[Map[iter, a, b, exn], exn]: ...`
#[derive(ToDoc)]
type TraitImpl(
    # Free variables of the `impl`.
    #
    # In the example: `iter`, `a`, `b`.
    qvars: Vec[QVar],

    # Arguments of the trait.
    #
    # In the example: `[Map[iter, a, b], b]`, where `iter`, `a` and `b` are
    # `QVar`s in `qvars`.
    traitArgs: Vec[Ty],

    # Predicates of the implementation.
    #
    # In the example: `[(Iterator, [iter, a])]`, where `iter` and `a` are
    # `QVar`s in `qvars`.
    #
    # Note: these types should be instantiated together with `traitArgs` so that
    # the same `QVar` in arguments and preds will be the same instantiated type
    # variable, and as we match args the preds will be updated.
    preds: Vec[TraitPred],
)


# Similar to `Pred`, but doesn't have a `Loc`.
#[derive(ToDoc)]
type TraitPred(
    trait_: TyDefIdx,
    params: Vec[Ty],
)


TraitImpl.tryMatch(self, args: Vec[Ty], varGen: UVarGen, loc: Loc) Option[Vec[Pred]]:
    if args.len() != self.traitArgs.len():
        panic(
            "`loc`: BUG: Number of arguments applied to the trait don't match the arity",
        )

    # Maps `QVar`s to instantiations.
    let varMap: HashMap[LocalId, Ty] = HashMap.fromIter(
        self.qvars.iter().map(
            \(qvar: QVar) (key: LocalId, val: Ty):
                let instantiatedVar = Ty.UVar(varGen.newVar(0, qvar.kind, loc))
                (key = qvar.id, val = instantiatedVar),
        ),
    )

    for argIdx: U32 in range(u32(0), self.traitArgs.len()):
        let implArg = self.traitArgs.get(argIdx)
        let tyArg = args.get(argIdx)
        let instantiatedImplArg = implArg.substQVars(varMap)
        if not unifyOneWay(instantiatedImplArg, tyArg, varGen, 0, loc):
            return Option.None

    Option.Some(
        Vec.fromIter(
            self.preds.iter().map(
                \(pred: TraitPred):
                    Pred(
                        trait_ = pred.trait_,
                        params =
                            Vec.fromIter(
                                args.iter().map(
                                    \(arg: Ty): arg.substQVars(varMap),
                                ),
                            ),
                        loc,
                    ),
            ),
        ),
    )
