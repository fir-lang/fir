use crate::ast;
use crate::collections::{Map, Set};
use crate::type_checker::loc_string;
use crate::type_checker::ty::*;

use smol_str::SmolStr;

/// Convert an AST type to type checking type.
///
/// `quantified_tys` are the type variables quantified in the context. These types will be
/// converted to `Ty::QVar`.
// TODO: Remove `quantified_tys` argument, map types to `Ty`s (instead of `TyCon`s) in the
// `ty_cons` argument.
pub fn convert_ast_ty(
    ty_cons: &Map<Id, TyCon>,
    quantified_tys: &Set<Id>,
    ast_ty: &ast::Type,
    loc: &ast::Loc,
) -> Ty {
    match ast_ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            if quantified_tys.contains(name) {
                if !args.is_empty() {
                    panic!(
                        "{}: Incorrect number of type arguments to quantified type {}: {} (expected 0)",
                        loc_string(loc),
                        name,
                        args.len()
                    );
                }
                return Ty::QVar(name.clone());
            }

            let con = match ty_cons.get(name) {
                Some(con) => con,
                None => panic!("{}: Unknown type {}", loc_string(loc), name),
            };
            if con.arity() as usize != args.len() {
                panic!(
                    "{}: Incorrect number of type arguments to {}, expected {}, found {}",
                    loc_string(loc),
                    name,
                    con.arity(),
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
                let ty = convert_ast_ty(ty_cons, quantified_tys, &ty.node, &ty.loc);
                match name {
                    Some(name) => {
                        let old = converted_named_args.insert(name.clone(), ty);
                        if old.is_some() {
                            panic!(
                                "{}: Associated type argument {} defined multiple times",
                                loc_string(loc),
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
                    loc_string(loc),
                );
            }

            if converted_args.is_empty() && converted_named_args.is_empty() {
                return Ty::Con(con.id.clone());
            }

            let args = if converted_named_args.is_empty() {
                TyArgs::Positional(converted_args)
            } else {
                TyArgs::Named(converted_named_args)
            };

            Ty::App(con.id.clone(), args)
        }

        ast::Type::Record(fields) => Ty::Record(
            fields
                .iter()
                .map(|named_ty| {
                    (
                        named_ty.name.as_ref().unwrap().clone(),
                        convert_ast_ty(ty_cons, quantified_tys, &named_ty.node, loc),
                    )
                })
                .collect(),
        ),

        ast::Type::AssocType(ast::AssocType { ty, assoc_ty }) => Ty::AssocTySelect {
            ty: Box::new(convert_ast_ty(ty_cons, quantified_tys, &ty.node, &ty.loc)),
            assoc_ty: assoc_ty.clone(),
        },
    }
}

/// Convert a function type to a `Scheme`.
///
/// - `ty_ty_params`: When converting associated functions or trait methods, type parameters of the type.
/// - `fun_ty_params`: Type parameters of the function.
pub(super) fn convert_fun_ty(
    self_ty: Option<&Ty>,
    ty_ty_params: &Set<Id>,
    fun_ty_params: &[ast::L<(ast::L<Id>, Vec<ast::L<ast::Type>>)>],
    params: &[(SmolStr, ast::L<ast::Type>)],
    return_ty: &Option<ast::L<ast::Type>>,
    loc: &ast::Loc,
    ty_cons: &Map<Id, TyCon>,
) -> Scheme {
    let quantified_ty_ids: Set<Id> = fun_ty_params
        .iter()
        .map(|ty_param| ty_param.node.0.node.clone())
        .collect();

    let mut quantified_vars: Vec<(Id, Map<Id, Map<Id, Ty>>)> =
        Vec::with_capacity(fun_ty_params.len());

    for ast::L {
        loc: _,
        node: ty_param,
    } in fun_ty_params
    {
        let mut trait_map: Map<Id, Map<Id, Ty>> = Default::default();

        for bound in &ty_param.1 {
            // Syntactically a bound should be in form: `Id[(Id = Ty),*]`.
            // Parser is more permissive, we check the syntax here.
            let (trait_id, assoc_tys) = match &bound.node {
                ast::Type::Named(ast::NamedType { name, args })
                    if args.iter().all(|arg| arg.node.0.is_some()) =>
                {
                    (
                        name.clone(),
                        args.iter()
                            .map(|arg| {
                                (
                                    arg.node.0.as_ref().unwrap().clone(),
                                    convert_ast_ty(
                                        ty_cons,
                                        &quantified_ty_ids,
                                        &arg.node.1.node,
                                        &arg.node.1.loc,
                                    ),
                                )
                            })
                            .collect(),
                    )
                }

                _ => panic!("{}: Invalid predicate syntax", loc_string(&bound.loc)),
            };

            let trait_con = match ty_cons.get(&trait_id) {
                Some(con) => con,
                None => panic!(
                    "{}: Type in bound {:?} is not a trait",
                    loc_string(&bound.loc),
                    trait_id
                ),
            };

            if !trait_con.is_trait() {
                panic!(
                    "{}: Type {} is not a trait",
                    loc_string(&bound.loc),
                    trait_id
                );
            }

            let old = trait_map.insert(trait_id.clone(), assoc_tys);
            if old.is_some() {
                panic!(
                    "{}: Bound {} is defined multiple times",
                    loc_string(&bound.loc),
                    trait_id
                );
            }
        }

        if quantified_vars.iter().any(|(id, _)| id == &ty_param.0.node) {
            panic!(
                "{}: Type variable {} is listed multiple times",
                loc_string(loc),
                ty_param.0.node,
            );
        }

        quantified_vars.push((ty_param.0.node.clone(), trait_map));
    }

    // Quantified variables of both the function and the type.
    let all_quantified_vars: Set<Id> = quantified_vars
        .iter()
        .map(|(param, _bounds)| param)
        .chain(ty_ty_params.iter())
        .cloned()
        .collect();

    let mut arg_tys: Vec<Ty> =
        Vec::with_capacity(params.len() + if self_ty.is_some() { 1 } else { 0 });

    if let Some(self_ty) = self_ty {
        arg_tys.push(self_ty.clone());
    }

    arg_tys.extend(
        params
            .iter()
            .map(|ty| convert_ast_ty(ty_cons, &all_quantified_vars, &ty.1.node, &ty.1.loc)),
    );

    let ret_ty = match return_ty {
        Some(ret_ty) => convert_ast_ty(ty_cons, &all_quantified_vars, &ret_ty.node, &ret_ty.loc),
        None => Ty::unit(),
    };

    let fun_ty = Ty::Fun(arg_tys, Box::new(ret_ty));

    Scheme {
        quantified_vars,
        ty: fun_ty,
        loc: loc.clone(),
    }
}

pub(super) fn convert_fields(
    ty_params: &Set<Id>,
    fields: &ast::ConstructorFields,
    ty_cons: &Map<Id, TyCon>,
    loc: &ast::Loc,
) -> Option<ConFields> {
    match fields {
        ast::ConstructorFields::Empty => None,
        ast::ConstructorFields::Named(named_fields) => Some(ConFields::Named(
            named_fields
                .iter()
                .map(|(name, ty)| (name.clone(), convert_ast_ty(ty_cons, ty_params, ty, loc)))
                .collect(),
        )),
        ast::ConstructorFields::Unnamed(fields) => Some(ConFields::Unnamed(
            fields
                .iter()
                .map(|ty| convert_ast_ty(ty_cons, ty_params, ty, loc))
                .collect(),
        )),
    }
}
