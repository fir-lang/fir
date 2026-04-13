use crate::ast::{self, Name};
use crate::collections::*;
use crate::type_checker::ModuleEnv;
use crate::type_checker::id::Id;
use crate::type_checker::loc_display;
use crate::type_checker::ty::*;
use crate::type_checker::ty_map::TyMap;

/// Convert an AST type to type checking type.
pub(super) fn convert_ast_ty(
    tys: &TyMap,
    module_env: &ModuleEnv,
    ast_ty: &ast::Type,
    loc: &ast::Loc,
) -> Ty {
    match ast_ty {
        ast::Type::Named(named_ty) => convert_named_ty(tys, module_env, named_ty, loc),

        ast::Type::Var(var) => tys
            .get_var(var)
            .unwrap_or_else(|| panic!("{}: Unknown type variable {}", loc_display(loc), var))
            .clone(),

        ast::Type::Record {
            fields,
            extension,
            is_row,
        } => {
            let mut labels: OrdMap<Name, Ty> = OrdMap::new();

            for (field_name, field_ty) in fields {
                let ty = convert_ast_ty(tys, module_env, field_ty, loc);
                let old = labels.insert(field_name.clone(), ty);
                if old.is_some() {
                    panic!(
                        "{}: Field {} defined multiple times in record",
                        loc_display(loc),
                        field_name
                    );
                }
            }

            let extension = match extension {
                Some(ext) => {
                    let ext_converted = convert_ast_ty(tys, module_env, &ext.node, &ext.loc);
                    if ext_converted.kind() != Kind::Row(RecordOrVariant::Record) {
                        panic!(
                            "{}: Record extension type {} has kind {}",
                            loc_display(&ext.loc),
                            &ext.node,
                            ext_converted.kind()
                        );
                    }
                    Some(Box::new(ext_converted))
                }
                None => None,
            };

            Ty::Record {
                labels,
                extension,
                is_row: *is_row,
            }
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row,
        } => {
            let mut labels: OrdMap<Id, Ty> = OrdMap::new();

            for alt in alts {
                let ty = convert_named_ty(tys, module_env, alt, loc);
                let alt_id = super::resolve_name(module_env, &alt.name);
                let old = labels.insert(alt_id, ty);
                if old.is_some() {
                    panic!(
                        "{}: Type {} used multiple times in variant type",
                        loc_display(loc),
                        alt.name
                    );
                }
            }

            let extension = match extension {
                Some(ext) => {
                    let ext_converted = convert_ast_ty(tys, module_env, &ext.node, &ext.loc);
                    if ext_converted.kind() != Kind::Row(RecordOrVariant::Variant) {
                        panic!(
                            "{}: Variant extension type {} has kind {}",
                            loc_display(&ext.loc),
                            &ext.node,
                            ext_converted.kind()
                        );
                    }
                    Some(Box::new(ext_converted))
                }
                None => None,
            };

            Ty::Variant {
                labels,
                extension,
                is_row: *is_row,
            }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            let args = FunArgs::Positional {
                args: args
                    .iter()
                    .map(|ty| convert_ast_ty(tys, module_env, &ty.node, &ty.loc))
                    .collect(),
            };

            let ret = Box::new(match ret {
                Some(ret) => convert_ast_ty(tys, module_env, &ret.node, &ret.loc),
                None => Ty::unit(),
            });

            let exceptions = exceptions.as_ref().unwrap_or_else(|| {
                panic!("{}: Function type without exception type", loc_display(loc))
            });

            let exceptions = Box::new(convert_ast_ty(
                tys,
                module_env,
                &exceptions.node,
                &exceptions.loc,
            ));

            Ty::Fun {
                args,
                ret,
                exceptions: Some(exceptions),
            }
        }

        ast::Type::AssocTySelect { ty, assoc_ty } => {
            let ty = convert_ast_ty(tys, module_env, &ty.node, &ty.loc);
            if let Ty::App(trait_, _trait_args, kind) = &ty {
                assert_eq!(*kind, Kind::Star);
                let kind = tys
                    .get_con(trait_)
                    .unwrap_or_else(|| {
                        panic!("{}: Unknown type {}", loc_display(loc), trait_.name())
                    })
                    .details
                    .trait_details()
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: Type {} is not a trait",
                            loc_display(loc),
                            trait_.name()
                        )
                    })
                    .assoc_tys
                    .get(assoc_ty)
                    .unwrap_or_else(|| {
                        panic!(
                            "{}: Trait {} does not have an associated type named {}",
                            loc_display(loc),
                            trait_.name(),
                            assoc_ty
                        )
                    })
                    .kind;
                Ty::AssocTySelect {
                    ty: Box::new(ty),
                    assoc_ty: assoc_ty.clone(),
                    kind,
                }
            } else {
                panic!(
                    "{}: Type in associated type selection is not a trait",
                    loc_display(loc)
                );
            }
        }
    }
}

fn convert_named_ty(
    tys: &TyMap,
    module_env: &ModuleEnv,
    named_ty: &ast::NamedType,
    loc: &ast::Loc,
) -> Ty {
    let ast::NamedType {
        mod_prefix: _,
        name,
        args,
    } = named_ty;

    let ty_con = tys
        .resolve(module_env, name)
        .unwrap_or_else(|| panic!("{}: Unknown type {}", loc_display(loc), name));

    if ty_con.arity() as usize != args.len() {
        panic!(
            "{}: Incorrect number of type arguments to {}, expected {}, found {}",
            loc_display(loc),
            name,
            ty_con.arity(),
            args.len()
        )
    }

    if let TyConDetails::Synonym(syn_ty) = &ty_con.details {
        let converted_args: Vec<Ty> = args
            .iter()
            .map(|arg| convert_ast_ty(tys, module_env, &arg.node, &arg.loc))
            .collect();
        let subst_map: HashMap<Name, Ty> = ty_con
            .ty_params
            .iter()
            .map(|(name, _)| name.clone())
            .zip(converted_args)
            .collect();
        return syn_ty.subst_qvars(&subst_map);
    }

    if args.is_empty() {
        return Ty::Con(ty_con.id.clone(), Kind::Star);
    }

    let converted_args: Vec<Ty> = args
        .iter()
        .map(|arg| convert_ast_ty(tys, module_env, &arg.node, &arg.loc))
        .collect();

    Ty::App(ty_con.id.clone(), converted_args, Kind::Star)
}

pub(super) fn convert_fields(
    tys: &TyMap,
    module_env: &ModuleEnv,
    fields: &ast::ConFields,
) -> Option<FunArgs> {
    match fields {
        ast::ConFields::Empty => None,
        ast::ConFields::Named { fields, extension } => Some(FunArgs::Named {
            args: fields
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        convert_ast_ty(tys, module_env, &ty.node, &ty.loc),
                    )
                })
                .collect(),
            extension: extension
                .as_ref()
                .map(|ext_ty| Box::new(convert_ast_ty(tys, module_env, &ext_ty.node, &ext_ty.loc))),
        }),
        ast::ConFields::Unnamed { fields } => Some(FunArgs::Positional {
            args: fields
                .iter()
                .map(|ty| convert_ast_ty(tys, module_env, &ty.node, &ty.loc))
                .collect(),
        }),
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum TyVarConversion {
    ToRVar,
    ToQVar,
}

/// Convert the context to type checking types, update `tys` (in the current scope) with the
/// context types.
pub(super) fn convert_and_bind_context(
    tys: &mut TyMap,
    module_env: &ModuleEnv,
    context_ast: &ast::Context,
    conversion: TyVarConversion,
) -> Vec<Pred> {
    let mut preds_converted: Vec<Pred> = Vec::with_capacity(context_ast.preds.len());

    // Bind type parameters.
    for (id, kind) in &context_ast.type_params {
        match conversion {
            TyVarConversion::ToRVar => {
                tys.insert_var(id.clone(), Ty::RVar(id.clone(), *kind));
            }
            TyVarConversion::ToQVar => {
                tys.insert_var(id.clone(), Ty::QVar(id.clone(), *kind));
            }
        }
    }

    // Convert preds.
    for ty in &context_ast.preds {
        if let Some(pred) = convert_pred(tys, module_env, &ty.node, &ty.loc) {
            preds_converted.push(pred);
        }
    }

    preds_converted
}

fn convert_pred(
    tys: &mut TyMap,
    module_env: &ModuleEnv,
    pred_ast: &ast::Pred,
    loc: &ast::Loc,
) -> Option<Pred> {
    match pred_ast {
        ast::Pred::Kind { .. } => {
            // Kind annotations are used by the kind inference. Kind inference could remove them
            // from the context, but at least for now we keep the list as-is and skip these here.
            None
        }

        ast::Pred::App(ast::NamedType {
            mod_prefix: _,
            name,
            args,
        }) => Some(Pred {
            trait_: tys
                .resolve(module_env, name)
                .unwrap_or_else(|| panic!("{}: Unknown trait {}", loc_display(loc), name))
                .id
                .clone(),
            params: args
                .iter()
                .map(|arg| convert_ast_ty(tys, module_env, &arg.node, &arg.loc))
                .collect(),
            assoc_ty: None,
            loc: loc.clone(),
        }),

        ast::Pred::AssocTyEq {
            ty:
                ast::NamedType {
                    mod_prefix: _,
                    name,
                    args,
                },
            assoc_ty,
            eq,
        } => Some(Pred {
            trait_: tys
                .resolve(module_env, name)
                .unwrap_or_else(|| panic!("{}: Unknown trait {}", loc_display(loc), name))
                .id
                .clone(),
            params: args
                .iter()
                .map(|arg| convert_ast_ty(tys, module_env, &arg.node, &arg.loc))
                .collect(),
            assoc_ty: Some((
                assoc_ty.clone(),
                convert_ast_ty(tys, module_env, &eq.node, &eq.loc),
            )),
            loc: loc.clone(),
        }),
    }
}
