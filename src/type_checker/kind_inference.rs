/*
Simple kind inference: analyzes one declaration at a time, infers kind of a type parameter without
explicit kind annotation from the definition. If a type parameter is used in a row position its kind
is inferred. Otherwise it's defaulted as `*`.

Also adds a type parameter for the missing exception types in functions. E.g.

    foo(x: U32, y: U32) U32
    ==>
    foo[?exn: *](x: U32, y: U32) U32 / ?exn

*/

use crate::ast;
use crate::collections::*;
use crate::module_loader::LoadedPgm;
use crate::type_checker::convert::convert_kind;
use crate::type_checker::{Kind, Name, RecordOrVariant};

pub fn add_missing_type_params(pgm: &mut LoadedPgm) {
    for (_, decl) in pgm.iter_decls_mut() {
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
// When checking a `trait`, the updated kinds in `tvs` will be used as the kinds of the `trait` type
// parameters.
//
// When checking an `impl`, the kinds of type parameters in `tvs` should all be specified before
// calling this function.
fn add_missing_type_params_fun(
    sig: &mut ast::FunSig,
    tvs: &mut OrderMap<Name, Option<Kind>>,
    loc: &ast::Loc,
) {
    assert!(sig.context.type_params.is_empty());

    if sig.exceptions.is_none() {
        sig.exceptions = Some(exn_type(loc));
    }

    // Variables bound in the enclosing `trait` or `impl` context.
    let bound_vars: HashSet<Name> = tvs.keys().cloned().collect();

    for pred in &sig.context.preds {
        collect_pred_tvs(&pred.node, tvs);
    }
    match &sig.self_ {
        ast::SelfParam::No | ast::SelfParam::Implicit => {}
        ast::SelfParam::Explicit(ty) => {
            collect_tvs(&ty.node, tvs);
        }
    }
    for (_, param_ty) in &sig.params {
        if let Some(param_ty) = param_ty {
            collect_tvs(&param_ty.node, tvs);
        }
    }
    if let Some(ret) = &sig.return_ty {
        collect_tvs(&ret.node, tvs);
    }
    if let Some(exn) = &sig.exceptions {
        collect_tvs(&exn.node, tvs);
    }

    // NB. Do not use `Set::difference` here as that will change order of the type variables. We
    // want left-to-right order.
    for fv in tvs.keys() {
        if bound_vars.contains(fv) {
            continue;
        }
        let fv_kind = (*tvs.get(fv).unwrap()).unwrap_or(Kind::Star);
        sig.context.type_params.push(((*fv).clone(), fv_kind));
    }
}

fn add_missing_type_params_impl(decl: &mut ast::ImplDecl) {
    assert!(decl.context.type_params.is_empty()); // first time visiting this impl

    let mut impl_context_var_kinds: OrderMap<Name, Option<Kind>> = Default::default();

    for pred in &decl.context.preds {
        collect_pred_tvs(&pred.node, &mut impl_context_var_kinds);
    }

    for ty in &decl.tys {
        collect_tvs(&ty.node, &mut impl_context_var_kinds);
    }

    let impl_context_vars: OrderSet<Name> = impl_context_var_kinds.keys().cloned().collect();

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
            let kind = (*impl_context_var_kinds.get(&id).unwrap()).unwrap_or(Kind::Star);
            (id, kind)
        })
        .collect();
}

fn add_missing_type_params_trait(decl: &mut ast::TraitDecl) {
    assert!(decl.type_param_kinds.is_empty());

    let mut trait_context_var_kinds: OrderMap<Name, Option<Kind>> = Default::default();
    let mut trait_context_vars: HashSet<Name> = Default::default();

    for param in &decl.type_params {
        let kind = convert_kind(&param.kind);
        trait_context_var_kinds.insert(param.name.node.clone(), kind);
        trait_context_vars.insert(param.name.node.clone());
    }

    for item in &mut decl.items {
        match item {
            ast::TraitDeclItem::Type {
                name: _,
                kind: _,
                default,
            } => {
                if let Some(default) = default {
                    collect_tvs(&default.node, &mut trait_context_var_kinds);
                }
            }

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
            (*trait_context_var_kinds.get(&param.name.node).unwrap()).unwrap_or(Kind::Star)
        })
        .collect();
}

fn add_missing_type_params_type(ty: &mut ast::TypeDecl) {
    assert!(ty.type_param_kinds.is_empty());

    // `extern` types can only take `*` arguments.
    if let Some(ast::TypeDeclRhs::Extern(_)) = &ty.rhs {
        for _ in &ty.type_params {
            ty.type_param_kinds.push(Kind::Star);
        }
        return;
    }

    let mut type_param_kinds: OrderMap<Name, Option<Kind>> = Default::default();
    for param in &ty.type_params {
        type_param_kinds.insert(param.name.node.clone(), convert_kind(&param.kind));
    }

    match &ty.rhs {
        Some(ast::TypeDeclRhs::Product(fields)) => {
            collect_fields_tvs(fields, &mut type_param_kinds);
        }
        Some(ast::TypeDeclRhs::Sum { cons, extension }) => {
            for ast::ConDecl { name: _, fields } in cons.iter() {
                collect_fields_tvs(fields, &mut type_param_kinds);
            }
            collect_extension_tvs(extension, &mut type_param_kinds, RecordOrVariant::Variant);
        }
        Some(ast::TypeDeclRhs::Synonym(ty)) => {
            collect_tvs(&ty.node, &mut type_param_kinds);
        }
        Some(ast::TypeDeclRhs::Extern(_)) => {
            panic!() // handled above
        }
        None => {}
    }

    for param in &ty.type_params {
        let kind = *type_param_kinds.get(&param.name.node).unwrap();
        let kind = kind.unwrap_or(Kind::Star);
        ty.type_param_kinds.push(kind);
    }
}

/// Collect type variables in `ty` in `tvs`.
///
/// If a type variable is an argument to the special marker traits `RecRow` or `VarRow`, or the
/// variable is used in a row position, the kind of the type variable is added as a record or
/// variant row in `tvs`. Otherwise we don't specify the kind of the variable so that we can update
/// it as record or variant row when we see one of the marker traits later, or default the kind as
/// `*` if not.
pub fn collect_tvs(ty: &ast::Type, tvs: &mut OrderMap<Name, Option<Kind>>) {
    match ty {
        ast::Type::Named(named_ty) => collect_named_ty_tvs(named_ty, tvs),

        ast::Type::Var(var) => {
            tvs.entry(var.clone()).or_insert(None);
        }

        ast::Type::Record {
            fields,
            extension,
            is_row: _,
        } => {
            for (_field_name, field_ty) in fields {
                collect_tvs(&field_ty.node, tvs);
            }
            collect_extension_tvs(extension, tvs, RecordOrVariant::Record);
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row: _,
        } => {
            for alt in alts {
                collect_named_ty_tvs(alt, tvs);
            }
            collect_extension_tvs(extension, tvs, RecordOrVariant::Variant);
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                collect_tvs(&arg.node, tvs);
            }
            if let Some(ret) = ret {
                collect_tvs(&ret.node, tvs);
            }
            if let Some(exn) = exceptions {
                collect_tvs(&exn.node, tvs);
            }
        }

        ast::Type::AssocTySelect { ty, assoc_ty: _ } => {
            collect_tvs(&ty.node, tvs);
        }
    }
}

fn collect_named_ty_tvs(named_ty: &ast::NamedType, tvs: &mut OrderMap<Name, Option<Kind>>) {
    let ast::NamedType {
        mod_prefix: _,
        name: _,
        args,
    } = named_ty;
    for arg in args {
        collect_tvs(&arg.node, tvs);
    }
}

fn collect_pred_tvs(pred: &ast::Pred, tvs: &mut OrderMap<Name, Option<Kind>>) {
    match pred {
        ast::Pred::Kind { var, kind } => {
            let old = tvs.insert(var.clone(), convert_kind(kind));
            assert!(old.is_none());
        }
        ast::Pred::App(ty) => collect_named_ty_tvs(ty, tvs),
        ast::Pred::AssocTyEq {
            ty,
            assoc_ty: _,
            eq,
        } => {
            collect_named_ty_tvs(ty, tvs);
            collect_tvs(&eq.node, tvs);
        }
    }
}

fn collect_fields_tvs(fields: &ast::ConFields, tvs: &mut OrderMap<Name, Option<Kind>>) {
    match fields {
        ast::ConFields::Empty => {}
        ast::ConFields::Named { fields, extension } => {
            for (_, ty) in fields.iter() {
                collect_tvs(&ty.node, tvs);
            }
            collect_extension_tvs(extension, tvs, RecordOrVariant::Record);
        }
        ast::ConFields::Unnamed { fields } => {
            for ty in fields.iter() {
                collect_tvs(&ty.node, tvs);
            }
        }
    }
}

fn collect_extension_tvs(
    extension: &Option<Box<ast::L<ast::Type>>>,
    tvs: &mut OrderMap<Name, Option<Kind>>,
    record_or_variant: RecordOrVariant,
) {
    if let Some(ext) = extension {
        match &ext.node {
            ast::Type::Var(var) => {
                let old = tvs.insert(var.clone(), Some(Kind::Row(record_or_variant)));
                if let Some(Some(old)) = old
                    && old != Kind::Row(record_or_variant)
                {
                    panic!("{}: Conflicting kind of type variable {}", ext.loc, var,);
                }
            }
            other => collect_tvs(other, tvs),
        }
    }
}

// The default exception type: `?exn`.
fn exn_type(loc: &ast::Loc) -> ast::L<ast::Type> {
    ast::L {
        node: ast::Type::Var(EXN_QVAR_NAME),
        loc: loc.clone(),
    }
}

const EXN_QVAR_NAME: Name = Name::new_static("?exn");
