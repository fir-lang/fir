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

use crate::ast::{self, Id};
use crate::collections::*;
use crate::type_checker::convert::*;
use crate::type_checker::ty::*;
use crate::type_checker::ty_map::TyMap;
use crate::type_checker::unification::try_unify_one_way;
use crate::utils::loc_display;

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

pub fn collect_trait_env(pgm: &ast::Module, tys: &mut TyMap) -> TraitEnv {
    let mut env: TraitEnv = Default::default();

    for item in pgm {
        let impl_ = match &item.node {
            ast::TopDecl::Impl(impl_) => impl_,
            _ => continue,
        };

        let trait_id = impl_.node.trait_.node.clone();

        /*
        let ty_con = tys
            .get_con(&trait_id)
            .unwrap_or_else(|| panic!("{}: Undefined trait {}", loc_display(&impl_.loc), trait_id));

        let trait_details = ty_con.trait_details().unwrap_or_else(|| {
            panic!(
                "{}: Type {} is not a trait",
                loc_display(&impl_.loc),
                trait_id
            )
        });
        */

        let preds: Set<Pred> = convert_and_bind_context(
            tys,
            &impl_.node.context,
            TyVarConversion::ToQVar,
            &impl_.loc,
        );

        let trait_impl = TraitImpl {
            qvars: impl_.node.context.type_params.clone(),
            trait_args: impl_
                .node
                .tys
                .iter()
                .map(|ty| convert_ast_ty(tys, &ty.node, &ty.loc))
                .collect(),
            preds: preds
                .into_iter()
                .map(
                    |Pred {
                         trait_,
                         params,
                         loc: _,
                     }| (trait_, params),
                )
                .collect(),
        };

        env.entry(trait_id.clone()).or_default().push(trait_impl);
    }

    env
}

impl TraitImpl {
    /// Try to match the trait arguments. If successful, return new goals.
    pub fn try_match(
        &self,
        args: &[Ty],
        var_gen: &mut TyVarGen,
        tys: &TyMap,
        loc: &ast::Loc,
    ) -> Option<Vec<(Id, Vec<Ty>)>> {
        if args.len() != self.trait_args.len() {
            panic!(
                "{}: BUG: Number of arguments applied to the trait don't match the arity",
                loc_display(loc)
            );
        }

        // Maps `QVar`s to instantiations.
        let var_map: Map<Id, Ty> = self
            .qvars
            .iter()
            .map(|(qvar, kind)| {
                let instantiated_var = var_gen.new_var(0, kind.clone(), loc.clone());
                (qvar.clone(), Ty::Var(instantiated_var.clone()))
            })
            .collect();

        for (impl_arg, ty_arg) in self.trait_args.iter().zip(args.iter()) {
            let instantiated_impl_arg = impl_arg.subst_qvars(&var_map);
            if !try_unify_one_way(&instantiated_impl_arg, ty_arg, tys.cons(), var_gen, 0, loc) {
                return None;
            }
        }

        Some(
            self.preds
                .iter()
                .map(|(trait_, args)| {
                    (
                        trait_.clone(),
                        args.iter().map(|arg| arg.subst_qvars(&var_map)).collect(),
                    )
                })
                .collect(),
        )
    }
}
