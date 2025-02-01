use crate::ast;
use crate::collections::*;
use crate::type_checker::{Id, Kind, RecordOrVariant};
use crate::utils::loc_display;

pub fn add_missing_type_params(pgm: &mut ast::Module) {
    for decl in pgm {
        match &mut decl.node {
            ast::TopDecl::Fun(decl) => {
                add_missing_type_params_fun(&mut decl.node.sig, &mut Default::default(), &decl.loc)
            }

            ast::TopDecl::Impl(decl) => add_missing_type_params_impl(&mut decl.node),

            ast::TopDecl::Trait(decl) => add_missing_type_params_trait(&mut decl.node),

            ast::TopDecl::Type(decl) => add_missing_type_params_type(&mut decl.node),

            ast::TopDecl::Import(_) => {}
        }
    }
}

// `tvs` are the variables bound in the enclosing `trait` or `impl` context.
//
// When checking a `trait`, the updated kinds in `tvs` will be used as the kinds `trait` type
// parameters.
//
// When checking an `impl`, the kinds of type parameters in `tvs` should all be specified before
// calling this function.
fn add_missing_type_params_fun(
    sig: &mut ast::FunSig,
    tvs: &mut Map<Id, Option<Kind>>,
    _loc: &ast::Loc,
) {
    let bound_vars: Set<Id> = tvs.keys().cloned().collect();

    for pred in &sig.context.preds {
        collect_tvs(&pred.node, &pred.loc, tvs);
    }
    for (_, param_ty) in &sig.params {
        collect_tvs(&param_ty.node, &param_ty.loc, tvs);
    }
    if let Some(exn) = &sig.exceptions {
        collect_tvs(&exn.node, &exn.loc, tvs);
    }
    if let Some(ret) = &sig.return_ty {
        collect_tvs(&ret.node, &ret.loc, tvs);
    }

    let tvs_set: Set<Id> = tvs.keys().cloned().collect();

    let diff = tvs_set.difference(&bound_vars);

    for fv in diff {
        let fv_kind = tvs.get(fv).unwrap().clone().unwrap_or(Kind::Star);
        sig.context.type_params.push(((*fv).clone(), fv_kind));
    }
}

fn add_missing_type_params_impl(decl: &mut ast::ImplDecl) {
    assert!(decl.context.type_params.is_empty()); // first time visiting this impl

    let mut impl_context_var_kinds: Map<Id, Option<Kind>> = Default::default();
    for pred in &decl.context.preds {
        collect_tvs(&pred.node, &pred.loc, &mut impl_context_var_kinds);
    }

    // Default kinds before checking functions.
    impl_context_var_kinds
        .values_mut()
        .for_each(|kind| *kind = Some(kind.clone().unwrap_or(Kind::Star)));

    let impl_context_vars: Set<Id> = impl_context_var_kinds.keys().cloned().collect();

    for fun in &mut decl.items {
        add_missing_type_params_fun(&mut fun.node.sig, &mut impl_context_var_kinds, &fun.loc);

        // Drop function variables added to the map.
        impl_context_var_kinds.retain(|id, _| impl_context_vars.contains(id));
    }

    decl.context.type_params = impl_context_vars
        .into_iter()
        .map(|id| {
            let kind = impl_context_var_kinds.get(&id).unwrap().clone().unwrap();
            (id, kind)
        })
        .collect();
}

fn add_missing_type_params_trait(decl: &mut ast::TraitDecl) {
    assert!(decl.type_param_kinds.is_empty());

    let mut trait_context_var_kinds: Map<Id, Option<Kind>> = Default::default();
    let mut trait_context_vars: Set<Id> = Default::default();

    for param in &decl.type_params {
        trait_context_var_kinds.insert(param.node.clone(), None);
        trait_context_vars.insert(param.node.clone());
    }

    for fun in &mut decl.items {
        add_missing_type_params_fun(&mut fun.node.sig, &mut trait_context_var_kinds, &fun.loc);

        // Drop function variables added to the map.
        trait_context_var_kinds.retain(|id, _| trait_context_vars.contains(id));
    }

    decl.type_param_kinds = decl
        .type_params
        .iter()
        .map(|id| {
            trait_context_var_kinds
                .get(&id.node)
                .unwrap()
                .clone()
                .unwrap_or(Kind::Star)
        })
        .collect();
}

fn add_missing_type_params_type(ty: &mut ast::TypeDecl) {
    // Make all parameters `*` for now. If we need different kinds we can add a suffix/prefix to the
    // name. At some point we should implement proper kind inference.
    ty.type_param_kinds = std::iter::repeat_with(|| Kind::Star)
        .take(ty.type_params.len())
        .collect();
}

const REC_ROW_TRAIT_ID: Id = Id::new_static("RecRow");
const VAR_ROW_TRAIT_ID: Id = Id::new_static("VarRow");

/// Collect type variables in `ty` in `tvs`.
///
/// If a type variable is an argument to the special marker traits `RecRow` or `VarRow`, or the
/// variable is used in a row position, the kind of the type variable is added as a record or
/// variant row in `tvs`. Otherwise we don't specify the kind of the variable so that we can update
/// it as record or variant row when we see one of the marker traits later, or default the kind as
/// `*` if not.
fn collect_tvs(ty: &ast::Type, loc: &ast::Loc, tvs: &mut Map<Id, Option<Kind>>) {
    match ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            if *name == REC_ROW_TRAIT_ID || *name == VAR_ROW_TRAIT_ID {
                let kind = if *name == REC_ROW_TRAIT_ID {
                    Kind::Row(RecordOrVariant::Record)
                } else {
                    Kind::Row(RecordOrVariant::Variant)
                };
                assert_eq!(args.len(), 1);
                match &args[0].node {
                    ast::Type::Var(var) => {
                        let old = tvs.insert(var.clone(), Some(kind.clone()));
                        if let Some(Some(old)) = old {
                            if old != kind {
                                panic!(
                                    "{}: Conflicting kind of type variable {}",
                                    loc_display(loc),
                                    var,
                                );
                            }
                        }
                    }
                    _ => panic!(
                        "{}: RecRow argument needs to be a type variable",
                        loc_display(loc)
                    ),
                }
                return;
            }

            for arg in args {
                collect_tvs(&arg.node, &arg.loc, tvs);
            }
        }

        ast::Type::Var(var) => {
            tvs.entry(var.clone()).or_insert(None);
        }

        ast::Type::Record { fields, extension } => {
            for field in fields {
                collect_tvs(&field.node, loc, tvs);
            }
            if let Some(ext) = extension {
                let old = tvs.insert(ext.clone(), Some(Kind::Row(RecordOrVariant::Record)));
                if let Some(Some(old)) = old {
                    if old != Kind::Row(RecordOrVariant::Record) {
                        panic!(
                            "{}: Conflicting kind of type variable {}",
                            loc_display(loc),
                            ext,
                        );
                    }
                }
            }
        }

        ast::Type::Variant { alts, extension } => {
            for alt in alts {
                for field in &alt.fields {
                    collect_tvs(&field.node, loc, tvs);
                }
            }
            if let Some(ext) = extension {
                let old = tvs.insert(ext.clone(), Some(Kind::Row(RecordOrVariant::Variant)));
                if let Some(Some(old)) = old {
                    if old != Kind::Row(RecordOrVariant::Variant) {
                        panic!(
                            "{}: Conflicting kind of type variable {}",
                            loc_display(loc),
                            ext,
                        );
                    }
                }
            }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                collect_tvs(&arg.node, &arg.loc, tvs);
            }
            if let Some(ret) = ret {
                collect_tvs(&ret.node, &ret.loc, tvs);
            }
            if let Some(exn) = exceptions {
                collect_tvs(&exn.node, &exn.loc, tvs);
            }
        }
    }
}
