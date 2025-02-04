/*
Trait resolving:

Note: "matching" below means one-way unification.

1. Try to find a trait that matches the goal in the current asumptions.
2. Check trait impls in the trait env:
    - For each impl of the goal pred's trait, match arguments of the pred with the trait's arguments.
    - Add `preds` of the impl to the goals to solve.

Example:

    let vec: Vec[U32] = Vec.withCapacity(10)
    let vecIter: VecIter[U32] = vec.iter()
    let map: Map[VecIter[U32], U32, Str] = vecIter.map(fn(x) { x.toStr() })
    let x: Str = map.next()

When type checking the `next` call, we find the `Iterator.next`:

    [iter: *, item: *, Iterator[iter, item]] Fn(self: iter): Option[item]

- Unify `iter ~ Map[VecIter[U32], U32, Str]`, which generates the predicate:

      Iterator[Map[VecIter[U32], U32, Str]], item]

- Unify return value with the expected type which is `Str`. Predicate becomes:

      Iterator[Map[VecIter[U32], U32, Str]], Str]

  Note: Predicates are resolved after checking the whole function.

- Solving the predicate:

    - Find matching impl, which is

        [Iterator[iter, a]] Iterator[Map[iter, a, b], b]

    - Substituting the variables with types in the predicate:

        iter => VecIter[U32]
        a => U32
        b => Str

      The `impl` predicate becomes: `Iterator[VecIter[U32], U32]` which we add to the goals.

- Solving the new goal works the same way:

    - Find matching impl, which is

        Iterator[VecIter[t], t]

    - Substitute variables with the types:

        t => U32

    - The impl doesn't have predicates, so we're done.
*/

use crate::ast::Id;
use crate::collections::*;
use crate::type_checker::ty::{Kind, Ty};

/// Maps trait ids to implementations.
pub type TraitEnv = Map<Id, Vec<TraitImpl>>;

#[derive(Debug)]
pub struct TraitImpl {
    // Example: `impl[Iterator[iter, a]] Iterator[Map[iter, a, b], b]: ...`

    // Free variables in the `impl`.
    //
    // In the example: `iter`, `a`, `b`.
    pub qvars: Vec<(Id, Kind)>,

    // Arguments of the trait.
    //
    // In the example: `[Map[iter, a, b], b]`, where `iter`, `a` and `b` are `QVar`s in `qvars`.
    pub trait_args: Vec<Ty>,

    // Predicates of the implementation.
    //
    // In the example: `[(Iterator, [iter, a])]`, where `iter` and `a` are `QVar`s in `qvars`.
    //
    // Note: these types should be instantiated together with `trait_args` so that the same `QVar`
    // in arguments and preds will be the same instantiated type variable, and as we match args
    // the preds will be updated.
    pub preds: Vec<(Id, Vec<Ty>)>,
}
