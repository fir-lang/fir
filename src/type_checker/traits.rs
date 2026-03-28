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
pub type TraitEnv = HashMap<Id, Vec<TraitImpl>>;

/// Example:
/// ```text
/// impl[Iterator[iter, exn], Iterator[iter, exn].Item = a] Iterator[Map[iter, a, b, exn], exn]:
///     type Item = b
///     next(self: Map[iter, a, b, exn]) Option[b] / exn
/// ```
#[derive(Debug)]
pub struct TraitImpl {
    /// Free variables of the `impl`.
    ///
    /// In the example: `iter`, `exn`, `a`, `b`.
    pub qvars: Vec<(Id, Kind)>,

    /// Arguments of the trait.
    ///
    /// In the example: `[Map[iter, a, b, exn], exn]`, where `iter`, `a`, `b`, `exn` are `QVar`s in
    /// `qvars`.
    pub trait_args: Vec<Ty>,

    /// Predicates of the implementation.
    ///
    /// In the example: `[(Iterator, [iter, exn])]`, where `iter` and `exn` are `QVar`s in `qvars`.
    ///
    /// Note: these types should be instantiated together with `trait_args` so that the same `QVar`
    /// in arguments and preds will be the same instantiated type variable, and as we match args
    /// the preds will be updated.
    pub preds: Vec<Pred>,

    /// Associated type equalities of the implementation.
    ///
    /// In the example: `Iterator[iter, exn].Item = a`, where `iter`, `exn`, and `a` are `QVar`s in
    /// `qvars`.
    ///
    /// Similar to `preds`, these types should be instantiated together with `trait_args`.
    /// pub eqs:
    pub assoc_tys: HashMap<Id, Ty>,
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

        tys.enter_scope();

        let preds: Vec<Pred> =
            convert_and_bind_context(tys, &impl_.node.context, TyVarConversion::ToQVar);

        let trait_impl = TraitImpl {
            qvars: impl_.node.context.type_params.clone(),
            trait_args: impl_
                .node
                .tys
                .iter()
                .map(|ty| convert_ast_ty(tys, &ty.node, &ty.loc))
                .collect(),
            preds,
            // TODO: Check that an assoc type is not defined multiple times.
            assoc_tys: impl_
                .node
                .items
                .iter()
                .filter_map(|item| match item {
                    ast::ImplDeclItem::Type { assoc_ty, rhs } => Some((
                        assoc_ty.node.clone(),
                        convert_ast_ty(tys, &rhs.node, &rhs.loc),
                    )),
                    ast::ImplDeclItem::Fun(_) => None,
                })
                .collect(),
        };

        tys.exit_scope();

        env.entry(trait_id.clone()).or_default().push(trait_impl);
    }

    env
}

impl TraitImpl {
    /// Try to match the trait arguments. If successful, return new goals and associated types of
    /// the matching implementation.
    pub(super) fn try_match(
        &self,
        args: &[Ty],
        var_gen: &UVarGen,
        cons: &HashMap<Id, TyCon>,
        loc: &ast::Loc,
    ) -> Option<(Vec<Pred>, HashMap<Id, Ty>)> {
        if args.len() != self.trait_args.len() {
            panic!(
                "{}: BUG: Number of arguments applied to the trait don't match the arity",
                loc_display(loc)
            );
        }

        // Maps `QVar`s to instantiations.
        let var_map: HashMap<Id, Ty> = self
            .qvars
            .iter()
            .map(|(qvar, kind)| {
                let instantiated_var = var_gen.new_var(0, kind.clone(), loc.clone());
                (qvar.clone(), Ty::UVar(instantiated_var.clone()))
            })
            .collect();

        for (impl_arg, ty_arg) in self.trait_args.iter().zip(args.iter()) {
            let instantiated_impl_arg = impl_arg.subst_qvars(&var_map);
            if !try_unify_one_way(&instantiated_impl_arg, ty_arg, cons, var_gen, 0, loc) {
                return None;
            }
        }

        let assoc_tys: HashMap<Id, Ty> = self
            .assoc_tys
            .iter()
            .map(|(assoc_ty, rhs)| (assoc_ty.clone(), rhs.subst_qvars(&var_map)))
            .collect();

        Some((
            self.preds
                .iter()
                .map(
                    |Pred {
                         trait_,
                         params,
                         assoc_ty,
                         loc: _,
                     }| Pred {
                        trait_: trait_.clone(),
                        params: params.iter().map(|arg| arg.subst_qvars(&var_map)).collect(),
                        assoc_ty: assoc_ty
                            .as_ref()
                            .map(|(id, ty)| (id.clone(), ty.subst_qvars(&var_map))),
                        loc: loc.clone(),
                    },
                )
                .collect(),
            assoc_tys,
        ))
    }
}
