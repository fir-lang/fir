use crate::ast;
use crate::collections::{Map, Set};
use crate::type_checker::loc_string;
use crate::type_checker::ty::*;

use smol_str::SmolStr;

/// Convert an AST type to type checking type.
///
/// `quantified_tys` are the type variables quantified in the context. These types will be
/// converted to `Ty::QVar`.
pub fn convert_ast_ty(
    ty_cons: &Map<Id, TyCon>,
    quantified_tys: &Set<Id>,
    ast_ty: &ast::Type,
    loc: &ast::Loc,
) -> Ty {
    match ast_ty {
        ast::Type::Named(ast::NamedType { name, args }) => match ty_cons.get(name) {
            Some(con) => {
                if con.arity() as usize != args.len() {
                    panic!(
                        "{}: Incorrect number of type arguments, expected {}, found {}",
                        loc_string(loc),
                        con.arity(),
                        args.len()
                    )
                }

                let args: Vec<Ty> = args
                    .iter()
                    .map(|ty| convert_ast_ty(ty_cons, quantified_tys, &ty.node, &ty.loc))
                    .collect();

                if args.is_empty() {
                    Ty::Con(name.clone())
                } else {
                    Ty::App(name.clone(), args)
                }
            }
            None => {
                if quantified_tys.contains(name) {
                    Ty::QVar(name.clone())
                } else {
                    panic!("{}: Unknown type {}", loc_string(loc), name)
                }
            }
        },

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
    fun_ty_params: &[ast::L<(ast::L<Id>, Vec<ast::L<Id>>)>],
    params: &[(SmolStr, ast::L<ast::Type>)],
    return_ty: &Option<ast::L<ast::Type>>,
    loc: &ast::Loc,
    ty_cons: &Map<Id, TyCon>,
) -> Scheme {
    let quantified_vars: Vec<(Id, Vec<Id>)> = fun_ty_params
        .iter()
        .map(
            |ast::L {
                 node: (ty, bounds),
                 loc: _,
             }| {
                (
                    ty.node.clone(),
                    bounds
                        .iter()
                        .map(|bound| {
                            if !ty_cons.contains_key(&bound.node) {
                                panic!();
                            }
                            bound.node.clone()
                        })
                        .collect(),
                )
            },
        )
        .collect();

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
