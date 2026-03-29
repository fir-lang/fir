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

            ast::TopDecl::Impl(decl) => add_missing_type_params_impl(&mut decl.node, &decl.loc),

            ast::TopDecl::Trait(decl) => add_missing_type_params_trait(&mut decl.node, &decl.loc),

            ast::TopDecl::Type(decl) => add_missing_type_params_type(&mut decl.node),

            ast::TopDecl::Import(_) => {}
        }
    }
}

// `tvs` are the variables bound in the enclosing `trait` or `impl` context.
//
// When checking a `trait`, the updated kinds in `tvs` will be used as the kinds of the `trait` type
// parameters.
//
// When checking an `impl`, the kinds of type parameters in `tvs` should all be specified before
// calling this function.
fn add_missing_type_params_fun(
    sig: &mut ast::FunSig,
    tvs: &mut OrderMap<Id, Option<Kind>>,
    _loc: &ast::Loc,
) {
    assert!(sig.context.type_params.is_empty());

    // Variables bound in the enclosing `trait` or `impl` context.
    let bound_vars: HashSet<Id> = tvs.keys().cloned().collect();

    for pred in &sig.context.preds {
        collect_pred_tvs(&pred.node, &pred.loc, tvs);
    }
    match &sig.self_ {
        ast::SelfParam::No | ast::SelfParam::Implicit => {}
        ast::SelfParam::Explicit(ty) => {
            collect_tvs(&ty.node, &ty.loc, tvs);
        }
    }
    for (_, param_ty) in &sig.params {
        if let Some(param_ty) = param_ty {
            collect_tvs(&param_ty.node, &param_ty.loc, tvs);
        }
    }
    if let Some(ret) = &sig.return_ty {
        collect_tvs(&ret.node, &ret.loc, tvs);
    }
    if let Some(exn) = &sig.exceptions {
        collect_tvs(&exn.node, &exn.loc, tvs);
    }

    // NB. Do not use `Set::difference` here as that will change order of the type variables. We
    // want left-to-right order.
    for fv in tvs.keys() {
        if bound_vars.contains(fv) {
            continue;
        }
        let fv_kind = tvs.get(fv).unwrap().clone().unwrap_or(Kind::Star);
        sig.context.type_params.push(((*fv).clone(), fv_kind));
    }
}

fn add_missing_type_params_impl(decl: &mut ast::ImplDecl, _loc: &ast::Loc) {
    assert!(decl.context.type_params.is_empty()); // first time visiting this impl

    let mut impl_context_var_kinds: OrderMap<Id, Option<Kind>> = Default::default();

    for pred in &decl.context.preds {
        collect_pred_tvs(&pred.node, &pred.loc, &mut impl_context_var_kinds);
    }

    for ty in &decl.tys {
        collect_tvs(&ty.node, &ty.loc, &mut impl_context_var_kinds);
    }

    let impl_context_vars: OrderSet<Id> = impl_context_var_kinds.keys().cloned().collect();

    for item in &mut decl.items {
        match item {
            ast::ImplDeclItem::Type { .. } => {}
            ast::ImplDeclItem::Fun(fun) => {
                add_missing_type_params_fun(
                    &mut fun.node.sig,
                    &mut impl_context_var_kinds,
                    &fun.loc,
                );

                // Drop function variables added to the map.
                impl_context_var_kinds.retain(|id, _| impl_context_vars.contains(id));
            }
        }
    }

    decl.context.type_params = impl_context_vars
        .into_iter()
        .map(|id| {
            let kind = impl_context_var_kinds
                .get(&id)
                .unwrap()
                .clone()
                .unwrap_or(Kind::Star);
            (id, kind)
        })
        .collect();
}

fn add_missing_type_params_trait(decl: &mut ast::TraitDecl, _loc: &ast::Loc) {
    assert!(decl.type_param_kinds.is_empty());

    let mut trait_context_var_kinds: OrderMap<Id, Option<Kind>> = Default::default();
    let mut trait_context_vars: HashSet<Id> = Default::default();

    for param in &decl.type_params {
        let kind = convert_kind(&param.kind);
        trait_context_var_kinds.insert(param.name.node.clone(), Some(kind));
        trait_context_vars.insert(param.name.node.clone());
    }

    for item in &mut decl.items {
        match item {
            ast::TraitDeclItem::Type { .. } => {}
            ast::TraitDeclItem::Fun(fun) => {
                add_missing_type_params_fun(
                    &mut fun.node.sig,
                    &mut trait_context_var_kinds,
                    &fun.loc,
                );

                // Drop function variables added to the map.
                trait_context_var_kinds.retain(|id, _| trait_context_vars.contains(id));
            }
        }
    }

    decl.type_param_kinds = decl
        .type_params
        .iter()
        .map(|param| {
            trait_context_var_kinds
                .get(&param.name.node)
                .unwrap()
                .clone()
                .unwrap_or(Kind::Star)
        })
        .collect();
}

fn add_missing_type_params_type(ty: &mut ast::TypeDecl) {
    assert!(ty.type_param_kinds.is_empty());
    ty.type_param_kinds.reserve(ty.type_params.len());
    for param in &ty.type_params {
        ty.type_param_kinds.push(convert_kind(&param.kind));
    }
}

pub(crate) const REC_ROW_TRAIT_ID: Id = Id::new_static("RecRow");
pub(crate) const VAR_ROW_TRAIT_ID: Id = Id::new_static("VarRow");

/// Collect type variables in `ty` in `tvs`.
///
/// If a type variable is an argument to the special marker traits `RecRow` or `VarRow`, or the
/// variable is used in a row position, the kind of the type variable is added as a record or
/// variant row in `tvs`. Otherwise we don't specify the kind of the variable so that we can update
/// it as record or variant row when we see one of the marker traits later, or default the kind as
/// `*` if not.
pub fn collect_tvs(ty: &ast::Type, loc: &ast::Loc, tvs: &mut OrderMap<Id, Option<Kind>>) {
    match ty {
        ast::Type::Named(named_ty) => collect_named_ty_tvs(named_ty, loc, tvs),

        ast::Type::Var(var) => {
            tvs.entry(var.clone()).or_insert(None);
        }

        ast::Type::Record {
            fields,
            extension,
            is_row: _,
        } => {
            for (_field_name, field_ty) in fields {
                collect_tvs(field_ty, loc, tvs);
            }
            if let Some(ext) = extension {
                match &ext.node {
                    ast::Type::Var(var) => {
                        let old = tvs.insert(var.clone(), Some(Kind::Row(RecordOrVariant::Record)));
                        if let Some(Some(old)) = old
                            && old != Kind::Row(RecordOrVariant::Record)
                        {
                            panic!(
                                "{}: Conflicting kind of type variable {}",
                                loc_display(loc),
                                var,
                            );
                        }
                    }
                    other => collect_tvs(other, &ext.loc, tvs),
                }
            }
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row: _,
        } => {
            for alt in alts {
                collect_named_ty_tvs(alt, loc, tvs);
            }
            if let Some(ext) = extension {
                match &ext.node {
                    ast::Type::Var(var) => {
                        let old =
                            tvs.insert(var.clone(), Some(Kind::Row(RecordOrVariant::Variant)));
                        if let Some(Some(old)) = old
                            && old != Kind::Row(RecordOrVariant::Variant)
                        {
                            panic!(
                                "{}: Conflicting kind of type variable {}",
                                loc_display(loc),
                                var,
                            );
                        }
                    }
                    other => collect_tvs(other, &ext.loc, tvs),
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

        ast::Type::AssocTySelect { ty, assoc_ty: _ } => {
            collect_tvs(&ty.node, &ty.loc, tvs);
        }
    }
}

fn collect_named_ty_tvs(
    named_ty: &ast::NamedType,
    loc: &ast::Loc,
    tvs: &mut OrderMap<Id, Option<Kind>>,
) {
    let ast::NamedType { name, args } = named_ty;

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
                if let Some(Some(old)) = old
                    && old != kind
                {
                    panic!(
                        "{}: Conflicting kind of type variable {}",
                        loc_display(loc),
                        var,
                    );
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

fn collect_pred_tvs(pred: &ast::Pred, loc: &ast::Loc, tvs: &mut OrderMap<Id, Option<Kind>>) {
    match pred {
        ast::Pred::Kind { var, kind } => {
            let old = tvs.insert(var.clone(), Some(convert_kind(kind)));
            assert!(old.is_none());
        }
        ast::Pred::App(ty) => collect_named_ty_tvs(ty, loc, tvs),
        ast::Pred::AssocTyEq {
            ty,
            assoc_ty: _,
            eq,
        } => {
            collect_named_ty_tvs(ty, loc, tvs);
            collect_tvs(&eq.node, &eq.loc, tvs);
        }
    }
}

fn convert_kind(kind: &Option<ast::L<ast::Type>>) -> Kind {
    let kind = match kind {
        Some(kind) => kind,
        None => return Kind::Star,
    };
    if let ast::Type::Named(ast::NamedType { name, args }) = &kind.node
        && name == "Row"
        && args.len() == 1
        && let ast::Type::Named(ast::NamedType {
            name: kind_arg_name,
            args: kind_arg_args,
        }) = &args[0].node
        && (kind_arg_name == "Rec" || kind_arg_name == "Var")
        && kind_arg_args.is_empty()
    {
        return Kind::Row(match kind_arg_name.as_str() {
            "Rec" => RecordOrVariant::Record,
            "Var" => RecordOrVariant::Variant,
            _ => unreachable!(),
        });
    }
    panic!(
        "{}: Kind annotation must be `Row[Rec]` (record row) or `Row[Var]` (variant row)",
        loc_display(&kind.loc)
    )
}
