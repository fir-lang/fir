use crate::ast::{self, Id};
use crate::collections::Map;
use crate::type_checker::loc_display;
use crate::type_checker::ty::*;
use crate::type_checker::ty_map::TyMap;

/*
Variations of function types:

Variation | Has type context | Has self type
----------+------------------+---------------
Top-level | No               | No
Assoc     | Yes              | Yes (concrete)
Trait     | Yes              | Yes (quantified)
Impl      | Yes              | Yes (concrete)

We don't do function type conversion here, functions should be converted manually using functions
here as helpers.
*/

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

            let mut converted_args: Vec<Ty> = Vec::with_capacity(args.len());
            let mut converted_named_args: Map<Id, Ty> = Default::default();

            for ast::L {
                loc: _,
                node: (name, ty),
            } in args
            {
                let ty = convert_ast_ty(tys, &ty.node, &ty.loc);
                match name {
                    Some(name) => {
                        let old = converted_named_args.insert(name.clone(), ty);
                        if old.is_some() {
                            panic!(
                                "{}: Associated type argument {} defined multiple times",
                                loc_display(loc),
                                name
                            );
                        }
                    }
                    None => {
                        converted_args.push(ty);
                    }
                }
            }

            if !converted_args.is_empty() && !converted_named_args.is_empty() {
                panic!(
                    "{}: Type cannot have both associated and positional arguments",
                    loc_display(loc),
                );
            }

            if converted_args.is_empty() && converted_named_args.is_empty() {
                return Ty::Con(ty_con.id.clone());
            }

            let args = if converted_named_args.is_empty() {
                TyArgs::Positional(converted_args)
            } else {
                TyArgs::Named(converted_named_args)
            };

            Ty::App(ty_con.id.clone(), args)
        }

        ast::Type::Var(var) => tys
            .get_var(var)
            .unwrap_or_else(|| panic!("{}: Unknown type variable {}", loc_display(loc), var))
            .clone(),

        ast::Type::Record { fields, extension } => {
            let mut ty_fields: Map<Id, Ty> =
                Map::with_capacity_and_hasher(fields.len(), Default::default());

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
            let mut ty_alts: Map<Id, Ty> =
                Map::with_capacity_and_hasher(alts.len(), Default::default());

            for ast::VariantAlt { con, fields } in alts {
                let mut record_labels: Map<Id, Ty> =
                    Map::with_capacity_and_hasher(fields.len(), Default::default());

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
    var_kinds: &Map<Id, Kind>,
    conversion: TyVarConversion,
    loc: &ast::Loc,
) -> Vec<(Id, QVar)> {
    // Bind type parameters.
    for ast::TypeParam { id, bounds: _ } in context_ast {
        let id = &id.node;
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

    let mut context_converted: Vec<(Id, QVar)> = Vec::with_capacity(context_ast.len());

    // Convert bounds.
    for ast::TypeParam { id: ty_var, bounds } in context_ast {
        let mut trait_map: Map<Id, Map<Id, Ty>> = Default::default();

        for bound in bounds {
            // Syntactically a bound should be in form: `Id ([(Id = Ty),*])?`.
            // Parser is more permissive, we check the syntax here.
            let (trait_id, assoc_tys) = convert_bound(tys, bound);
            let old = trait_map.insert(trait_id.clone(), assoc_tys);
            if old.is_some() {
                panic!(
                    "{}: Bound {} is defined multiple times",
                    loc_display(&bound.loc),
                    trait_id
                );
            }
        }

        if context_converted
            .iter()
            .any(|(qvar, _)| *qvar == ty_var.node)
        {
            panic!(
                "{}: Type variable {} is listed multiple times",
                loc_display(loc),
                ty_var.node,
            );
        }

        // TODO: Variables that don't appear in the arguments or return type won't have their kinds
        // inferred. Assume those to have kind `*`.
        // TODO FIXME HACK: Until we implement kind inference, handle `?exn` variables here.
        let kind = if ty_var.node == crate::type_checker::EXN_QVAR_ID {
            Kind::Row(RecordOrVariant::Variant)
        } else {
            var_kinds.get(&ty_var.node).cloned().unwrap_or(Kind::Star)
        };

        context_converted.push((
            ty_var.node.clone(),
            QVar {
                kind,
                bounds: trait_map,
            },
        ));
    }

    context_converted
}

/// Convert a bound in `<Id>[(<AssocTy> = <Ty>)*] form to (bound, associated types) pair.
pub(super) fn convert_bound(tys: &TyMap, bound: &ast::L<ast::Type>) -> (Id, Map<Id, Ty>) {
    let (trait_id, assoc_tys): (Id, Map<Id, Ty>) = match &bound.node {
        ast::Type::Named(ast::NamedType { name, args })
            if args.iter().all(|arg| arg.node.0.is_some()) =>
        {
            (
                name.clone(),
                args.iter()
                    .map(|arg| {
                        (
                            arg.node.0.as_ref().unwrap().clone(),
                            convert_ast_ty(tys, &arg.node.1.node, &arg.node.1.loc),
                        )
                    })
                    .collect(),
            )
        }

        _ => panic!("{}: Invalid predicate syntax", loc_display(&bound.loc)),
    };

    let trait_con = match tys.get_con(&trait_id) {
        Some(con) => con,
        None => panic!(
            "{}: Unknown type {} in bound",
            loc_display(&bound.loc),
            trait_id
        ),
    };

    if !trait_con.is_trait() {
        panic!(
            "{}: Type {} is not a trait",
            loc_display(&bound.loc),
            trait_id
        );
    }

    (trait_id, assoc_tys)
}
