use crate::ast::{self, Id};
use crate::collections::*;
use crate::type_checker::loc_display;
use crate::type_checker::ty::*;
use crate::type_checker::ty_map::TyMap;

/// Convert an AST type to type checking type.
pub(super) fn convert_ast_ty(tys: &TyMap, ast_ty: &ast::Type, loc: &ast::Loc) -> Ty {
    match ast_ty {
        ast::Type::Named(named_ty) => convert_named_ty(tys, named_ty, loc),

        ast::Type::Var(var) => tys
            .get_var(var)
            .unwrap_or_else(|| panic!("{}: Unknown type variable {}", loc_display(loc), var))
            .clone(),

        ast::Type::Record {
            fields,
            extension,
            is_row,
        } => {
            let mut ty_fields: OrdMap<Id, Ty> = OrdMap::new();

            for (field_name, field_ty) in fields {
                let ty = convert_ast_ty(tys, field_ty, loc);
                let old = ty_fields.insert(field_name.clone(), ty);
                if old.is_some() {
                    panic!(
                        "{}: Field {} defined multiple times in record",
                        loc_display(loc),
                        field_name
                    );
                }
            }

            Ty::Anonymous {
                labels: ty_fields,
                extension: extension
                    .as_ref()
                    .map(|ext_ty| Box::new(convert_ast_ty(tys, &ext_ty.node, &ext_ty.loc))),
                record_or_variant: RecordOrVariant::Record,
                is_row: *is_row,
            }
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row,
        } => {
            let mut ty_alts: OrdMap<Id, Ty> = OrdMap::new();

            for alt in alts {
                let ty = convert_named_ty(tys, alt, loc);
                let old = ty_alts.insert(alt.name.clone(), ty);
                if old.is_some() {
                    panic!(
                        "{}: Type {} used multiple times in variant type",
                        loc_display(loc),
                        alt.name
                    );
                }
            }

            Ty::Anonymous {
                labels: ty_alts,
                extension: extension
                    .as_ref()
                    .map(|ext_ty| Box::new(convert_ast_ty(tys, &ext_ty.node, &ext_ty.loc))),
                record_or_variant: RecordOrVariant::Variant,
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
                    .map(|ty| convert_ast_ty(tys, &ty.node, &ty.loc))
                    .collect(),
            };

            let ret = Box::new(match ret {
                Some(ret) => convert_ast_ty(tys, &ret.node, &ret.loc),
                None => Ty::unit(),
            });

            let exceptions = exceptions.as_ref().unwrap_or_else(|| {
                panic!("{}: Function type without exception type", loc_display(loc))
            });

            let exceptions = Box::new(convert_ast_ty(tys, &exceptions.node, &exceptions.loc));

            Ty::Fun {
                args,
                ret,
                exceptions: Some(exceptions),
            }
        }

        ast::Type::AssocTySelect { ty, assoc_ty } => Ty::AssocTySelect {
            ty: Box::new(convert_ast_ty(tys, &ty.node, &ty.loc)),
            assoc_ty: assoc_ty.clone(),
        },
    }
}

fn convert_named_ty(tys: &TyMap, named_ty: &ast::NamedType, loc: &ast::Loc) -> Ty {
    let ast::NamedType { name, args } = named_ty;

    if let Some(syn_ty) = tys.get_synonym(name) {
        if !args.is_empty() {
            panic!(
                "{}: Type synonym {} does not take type arguments",
                loc_display(loc),
                name
            );
        }
        return syn_ty.clone();
    }

    let ty_con = tys
        .get_con(name)
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

    if args.is_empty() {
        return Ty::Con(ty_con.id.clone(), Kind::Star);
    }

    let converted_args: Vec<Ty> = args
        .iter()
        .map(|arg| convert_ast_ty(tys, &arg.node, &arg.loc))
        .collect();

    Ty::App(ty_con.id.clone(), converted_args, Kind::Star)
}

pub(super) fn convert_fields(
    tys: &TyMap,
    fields: &ast::ConFields,
    loc: &ast::Loc,
) -> Option<FunArgs> {
    match fields {
        ast::ConFields::Empty => None,
        ast::ConFields::Named { fields, extension } => Some(FunArgs::Named {
            args: fields
                .iter()
                .map(|(name, ty)| (name.clone(), convert_ast_ty(tys, &ty.node, &ty.loc)))
                .collect(),
            extension: extension
                .as_ref()
                .map(|ext_ty| Box::new(convert_ast_ty(tys, &ext_ty.node, &ext_ty.loc))),
        }),
        ast::ConFields::Unnamed { fields } => Some(FunArgs::Positional {
            args: fields
                .iter()
                .map(|ty| convert_ast_ty(tys, &ty.node, &ty.loc))
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
    context_ast: &ast::Context,
    conversion: TyVarConversion,
) -> Vec<Pred> {
    let mut preds_converted: Vec<Pred> = Vec::with_capacity(context_ast.preds.len());

    // Bind type parameters.
    for (id, kind) in &context_ast.type_params {
        match conversion {
            TyVarConversion::ToRVar => {
                tys.insert_var(id.clone(), Ty::RVar(id.clone(), kind.clone()));
            }
            TyVarConversion::ToQVar => {
                tys.insert_var(id.clone(), Ty::QVar(id.clone(), kind.clone()));
            }
        }
    }

    // Convert preds.
    for ty in &context_ast.preds {
        let pred = convert_pred(tys, &ty.node, &ty.loc);
        preds_converted.push(pred);
    }

    preds_converted
}

fn convert_pred(tys: &mut TyMap, pred_ast: &ast::Pred, loc: &ast::Loc) -> Pred {
    match pred_ast {
        ast::Pred::App(ast::NamedType { name, args }) => Pred {
            trait_: name.clone(),
            params: args
                .iter()
                .map(|arg| convert_ast_ty(tys, &arg.node, &arg.loc))
                .collect(),
            assoc_ty: None,
            loc: loc.clone(),
        },

        ast::Pred::AssocTyEq {
            ty: ast::NamedType { name, args },
            assoc_ty,
            eq,
        } => Pred {
            trait_: name.clone(),
            params: args
                .iter()
                .map(|arg| convert_ast_ty(tys, &arg.node, &arg.loc))
                .collect(),
            assoc_ty: Some((assoc_ty.clone(), convert_ast_ty(tys, &eq.node, &eq.loc))),
            loc: loc.clone(),
        },
    }
}
