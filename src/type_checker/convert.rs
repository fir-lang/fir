use crate::ast::{self, Id};
use crate::collections::*;
use crate::type_checker::loc_display;
use crate::type_checker::ty::*;
use crate::type_checker::ty_map::TyMap;

/// Convert an AST type to type checking type.
pub(super) fn convert_ast_ty(tys: &TyMap, ast_ty: &ast::Type, loc: &ast::Loc) -> Ty {
    match ast_ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            // TODO FIXME HACK: `tys` is also used to map an associated type `T` (a `Type::Named`)
            // to `Self.T`, so we need to check var map here when converting a constructor.
            if let Some(ty) = tys.get_var(name) {
                assert!(args.is_empty());
                return ty.clone();
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

            let converted_args: Vec<Ty> = args
                .iter()
                .map(|arg| convert_ast_ty(tys, &arg.node, &arg.loc))
                .collect();

            if converted_args.is_empty() {
                return Ty::Con(ty_con.id.clone());
            }

            Ty::App(ty_con.id.clone(), converted_args)
        }

        ast::Type::Var(var) => tys
            .get_var(var)
            .unwrap_or_else(|| panic!("{}: Unknown type variable {}", loc_display(loc), var))
            .clone(),

        ast::Type::Record { fields, extension } => {
            let mut ty_fields: TreeMap<Id, Ty> = TreeMap::new();

            for ast::Named { name, node } in fields {
                let name = name.as_ref().unwrap_or_else(|| {
                    panic!(
                        "{}: Records with unnamed fields not supported yet",
                        loc_display(loc)
                    )
                });
                let ty = convert_ast_ty(tys, node, loc);
                let old = ty_fields.insert(name.clone(), ty);
                if old.is_some() {
                    panic!(
                        "{}: Field {} defined multiple times in record",
                        loc_display(loc),
                        name
                    );
                }
            }

            Ty::Anonymous {
                labels: ty_fields,
                extension: extension.as_ref().map(|var| match tys.get_var(var) {
                    Some(ty) => Box::new(ty.clone()),
                    None => panic!("{}: Unbound type variable {}", loc_display(loc), var),
                }),
                kind: RecordOrVariant::Record,
                is_row: false,
            }
        }

        ast::Type::Variant { alts, extension } => {
            let mut ty_alts: TreeMap<Id, Ty> = TreeMap::new();

            for ast::VariantAlt { con, fields } in alts {
                let mut record_labels: TreeMap<Id, Ty> = TreeMap::new();

                for ast::Named { name, node } in fields {
                    let name = name.as_ref().unwrap_or_else(|| {
                        panic!(
                            "{}: Variants with unnamed fields not supported yet",
                            loc_display(loc)
                        )
                    });
                    let ty = convert_ast_ty(tys, node, loc);
                    record_labels.insert(name.clone(), ty);
                }
                let record_ty = Ty::Anonymous {
                    labels: record_labels,
                    extension: None,
                    kind: RecordOrVariant::Record,
                    is_row: false,
                };

                let old = ty_alts.insert(con.clone(), record_ty);
                if old.is_some() {
                    panic!(
                        "{}: Constructor {} defined multiple times in variant",
                        loc_display(loc),
                        con
                    );
                }
            }

            Ty::Anonymous {
                labels: ty_alts,
                extension: extension.as_ref().map(|var| match tys.get_var(var) {
                    Some(ty) => Box::new(ty.clone()),
                    None => panic!("{}: Unbound type variable {}", loc_display(loc), var),
                }),
                kind: RecordOrVariant::Variant,
                is_row: false,
            }
        }

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => Ty::Fun {
            args: FunArgs::Positional(
                args.iter()
                    .map(|ty| convert_ast_ty(tys, &ty.node, &ty.loc))
                    .collect(),
            ),
            ret: Box::new(match ret {
                Some(ret) => convert_ast_ty(tys, &ret.node, &ret.loc),
                None => Ty::unit(),
            }),
            exceptions: exceptions
                .as_ref()
                .map(|ty| Box::new(convert_ast_ty(tys, &ty.node, &ty.loc))),
        },
    }
}

pub(super) fn convert_fields(
    tys: &TyMap,
    fields: &ast::ConstructorFields,
    loc: &ast::Loc,
) -> Option<ConFields> {
    match fields {
        ast::ConstructorFields::Empty => None,
        ast::ConstructorFields::Named(named_fields) => Some(ConFields::Named(
            named_fields
                .iter()
                .map(|(name, ty)| (name.clone(), convert_ast_ty(tys, ty, loc)))
                .collect(),
        )),
        ast::ConstructorFields::Unnamed(fields) => Some(ConFields::Unnamed(
            fields
                .iter()
                .map(|ty| convert_ast_ty(tys, ty, loc))
                .collect(),
        )),
    }
}

#[derive(Debug, Clone, Copy)]
pub(super) enum TyVarConversion {
    ToOpaque,
    ToQVar,
}

/// Convert the context to type checking types, update `tys` (in the current scope) with the
/// context types.
pub(super) fn convert_and_bind_context(
    tys: &mut TyMap,
    context_ast: &ast::Context,
    conversion: TyVarConversion,
    _loc: &ast::Loc,
) -> Set<Pred> {
    let mut preds_converted: Set<Pred> =
        Set::with_capacity_and_hasher(context_ast.preds.len(), Default::default());

    // Bind type parameters.
    for (id, _kind) in &context_ast.type_params {
        match conversion {
            TyVarConversion::ToOpaque => {
                tys.insert_con(id.clone(), TyCon::opaque(id.clone()));
                tys.insert_var(id.clone(), Ty::Con(id.clone()));
            }
            TyVarConversion::ToQVar => {
                tys.insert_var(id.clone(), Ty::QVar(id.clone()));
            }
        }
    }

    // Convert preds.
    for ty in &context_ast.preds {
        let pred = match convert_ast_ty(tys, &ty.node, &ty.loc) {
            Ty::App(con, args) => {
                // TODO: Check that `con` is a trait, arity and kinds match.
                Pred {
                    trait_: con,
                    params: args,
                    loc: ty.loc.clone(),
                }
            }
            _ => panic!("{}: Strange predicate syntax", loc_display(&ty.loc)),
        };
        preds_converted.insert(pred);
    }

    preds_converted
}
