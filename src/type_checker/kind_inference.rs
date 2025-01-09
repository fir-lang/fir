use crate::ast;
use crate::collections::{Map, Set};
use crate::type_checker::unification::unify;
use crate::type_checker::{FunArgs, Id, Kind, Ty, TyVar, TyVarGen, TyVarRef};
use crate::utils::loc_display;

use smol_str::SmolStr;

/*
No higher kinds for now.

Types, traits, and trait methods are checked together.

Functions are checked separately, so uses of types in function types cannot influence inferred kinds.

(TODO: I don't know why this is, but it's consistent with Haskell 98 kind inference.)

Trait methods need to be checked with the types to be able to infer the right kinds in cases like:

```
trait Blah[t]:
    fn f(a: [..t])
```

Without considering the function we cannot infer the kind of `t`.
*/
pub fn infer_kinds(pgm: &mut ast::Module) {
    let mut var_gen = TyVarGen::default();

    // `ty_arg_kinds[i]` maps type arguments of `types[i]` to their kinds.
    let mut ty_arg_kinds: Vec<Map<Id, Ty>> = vec![Default::default(); pgm.len()];

    // Maps type constructors to their kinds.
    let mut con_kinds: Map<Id, Ty> = Default::default();

    // Add kinds of type constructors, with unification variables as the parmaeter kinds.
    for (decl_idx, decl) in pgm.iter().enumerate() {
        match &decl.node {
            ast::TopDecl::Type(decl) => {
                let arity = decl.node.type_params.len();

                let arg_kind_vars: Vec<Ty> = std::iter::repeat_with(|| {
                    Ty::Var(var_gen.new_var(0, Kind::Star, decl.loc.clone()))
                })
                .take(arity)
                .collect();

                for (i, name) in decl.node.type_params.iter().enumerate() {
                    let old = ty_arg_kinds[decl_idx].insert(name.clone(), arg_kind_vars[i].clone());
                    assert!(old.is_none());
                }

                let old = con_kinds.insert(
                    decl.node.name.clone(),
                    Ty::Fun(
                        FunArgs::Positional(arg_kind_vars),
                        Box::new(TY_STAR.clone()),
                    ),
                );

                assert!(old.is_none());
            }

            ast::TopDecl::Trait(decl) => {
                let ty_var = Ty::Var(var_gen.new_var(0, Kind::Star, decl.loc.clone()));

                let old = con_kinds.insert(
                    decl.node.name.node.clone(),
                    Ty::Fun(
                        FunArgs::Positional(vec![ty_var.clone()]),
                        Box::new(TY_STAR.clone()),
                    ),
                );

                ty_arg_kinds[decl_idx].insert(decl.node.ty.id.node.clone(), ty_var);

                assert!(old.is_none());
            }

            ast::TopDecl::Impl(_) | ast::TopDecl::Fun(_) => {}

            ast::TopDecl::Import(_) => panic!(),
        }
    }

    // Unify kinds of parameters.
    for (decl_idx, decl) in pgm.iter().enumerate() {
        match &decl.node {
            ast::TopDecl::Type(decl) => {
                let rhs = match &decl.node.rhs {
                    Some(rhs) => rhs,
                    None => continue,
                };

                match rhs {
                    ast::TypeDeclRhs::Sum(cons) => {
                        for con in cons {
                            match &con.fields {
                                ast::ConstructorFields::Empty => {}

                                ast::ConstructorFields::Named(tys) => {
                                    tys.iter().for_each(|(_, ty)| {
                                        ty_kind(
                                            &con_kinds,
                                            &ty_arg_kinds[decl_idx],
                                            &mut var_gen,
                                            ty,
                                            &ast::Loc::dummy(),
                                        );
                                    });
                                }

                                ast::ConstructorFields::Unnamed(tys) => tys.iter().for_each(|ty| {
                                    ty_kind(
                                        &con_kinds,
                                        &ty_arg_kinds[decl_idx],
                                        &mut var_gen,
                                        ty,
                                        &ast::Loc::dummy(),
                                    );
                                }),
                            }
                        }
                    }

                    ast::TypeDeclRhs::Product(fields) => match fields {
                        ast::ConstructorFields::Empty => {}

                        ast::ConstructorFields::Named(tys) => {
                            tys.iter().for_each(|(_, ty)| {
                                ty_kind(
                                    &con_kinds,
                                    &ty_arg_kinds[decl_idx],
                                    &mut var_gen,
                                    ty,
                                    &ast::Loc::dummy(),
                                );
                            });
                        }

                        ast::ConstructorFields::Unnamed(tys) => tys.iter().for_each(|ty| {
                            ty_kind(
                                &con_kinds,
                                &ty_arg_kinds[decl_idx],
                                &mut var_gen,
                                ty,
                                &ast::Loc::dummy(),
                            );
                        }),
                    },
                }
            }

            ast::TopDecl::Fun(a) => todo!(),

            ast::TopDecl::Trait(l) => todo!(),

            ast::TopDecl::Impl(l) => todo!(),

            ast::TopDecl::Import(_) => {}
        }
    }

    let types: Vec<TypeDecl> = collect_types(pgm);
}

// con_kinds: Kinds of type constructors.
// arg_kinds: Kinds of type parameters of the current declaration.
fn ty_kind(
    con_kinds: &Map<Id, Ty>,
    arg_kinds: &Map<Id, Ty>,
    var_gen: &mut TyVarGen,
    ty: &ast::Type,
    loc: &ast::Loc,
) -> Ty {
    match ty {
        ast::Type::Named(ast::NamedType { name, args }) => {
            let con_fn = con_kinds.get(name).unwrap_or_else(|| {
                panic!("{}: Unbound type constructor {}", loc_display(loc), name)
            });

            match con_fn {
                Ty::Con(_) => {
                    assert_eq!(args.len(), 0);
                    TY_STAR.clone()
                }

                Ty::Fun(ty_con_args, ty_con_ret) => {
                    let ty_con_args = match ty_con_args {
                        FunArgs::Positional(args) => args,
                        FunArgs::Named(_) => panic!(),
                    };

                    assert_eq!(ty_con_args.len(), args.len());

                    for (ty_con_arg, arg) in ty_con_args.iter().zip(args.iter()) {
                        let arg_ty = ty_kind(
                            con_kinds,
                            arg_kinds,
                            var_gen,
                            &arg.node.1.node,
                            &arg.node.1.loc,
                        );
                        unify(
                            &ty_con_arg,
                            &arg_ty,
                            &Default::default(),
                            var_gen,
                            0,
                            &arg.node.1.loc,
                        );
                    }

                    (**ty_con_ret).clone()
                }

                _ => panic!(),
            }
        }

        ast::Type::Var(var) => arg_kinds
            .get(var)
            .cloned()
            .unwrap_or_else(|| panic!("{}: Unbound type variable: {}", loc_display(loc), var)),

        ast::Type::Record { fields, extension } => {
            for field in fields {
                ty_kind(con_kinds, arg_kinds, var_gen, &field.node, loc);
            }

            if let Some(ext) = extension {
                let ext_kind = arg_kinds.get(ext).unwrap_or_else(|| {
                    panic!("{}: Unbound type variable: {}", loc_display(loc), ext,)
                });
                unify(
                    ext_kind,
                    &TY_RECORD_ROW,
                    &Default::default(),
                    var_gen,
                    0,
                    loc,
                );
            }

            TY_STAR.clone()
        }

        ast::Type::Variant { alts, extension } => {
            for alt in alts {
                for field in &alt.fields {
                    ty_kind(con_kinds, arg_kinds, var_gen, &field.node, loc);
                }
            }

            if let Some(ext) = extension {
                let ext_kind = arg_kinds.get(ext).unwrap_or_else(|| {
                    panic!("{}: Unbound type variable: {}", loc_display(loc), ext,)
                });
                unify(
                    ext_kind,
                    &TY_VARIANT_ROW,
                    &Default::default(),
                    var_gen,
                    0,
                    loc,
                );
            }

            TY_STAR.clone()
        }

        ast::Type::Fn(ast::FnType { args, ret }) => {
            for arg in args {
                ty_kind(con_kinds, arg_kinds, var_gen, &arg.node, &arg.loc);
            }

            if let Some(ret) = ret {
                ty_kind(con_kinds, arg_kinds, var_gen, &ret.node, &ret.loc);
            }

            TY_STAR.clone()
        }
    }
}

// Base types of type inference are `*`, `row(record)`, `row(variant)`, and function types
// (`Ty::Fun`).
const TY_STAR: Ty = Ty::Con(SmolStr::new_static("*"));
const TY_RECORD_ROW: Ty = Ty::Con(SmolStr::new_static("row(record)"));
const TY_VARIANT_ROW: Ty = Ty::Con(SmolStr::new_static("row(variant)"));

/// A type declaration, abstracted for the purposes of kind inference.
#[derive(Debug, Clone)]
struct TypeDecl {
    /// Type constructor.
    con: Id,

    /// Type constructor arguments with inferred kinds.
    ///
    /// These get assigned fresh unification variables. At the end of the inference, variables that
    /// are not constrained are defaulted as `*`.
    args: Set<Id>,
}

fn collect_types(pgm: &ast::Module) -> Vec<TypeDecl> {
    fn type_decl(decl: &ast::TypeDecl) -> TypeDecl {
        todo!()
    }

    fn trait_decl(decl: &ast::TraitDecl) -> TypeDecl {
        todo!()
    }

    fn impl_decl(decl: &ast::ImplDecl) -> TypeDecl {
        todo!()
    }

    pgm.iter()
        .filter_map(|decl| match &decl.node {
            ast::TopDecl::Type(d) => Some(type_decl(&d.node)),

            ast::TopDecl::Trait(d) => Some(trait_decl(&d.node)),

            ast::TopDecl::Impl(d) => Some(impl_decl(&d.node)),

            ast::TopDecl::Fun(_) => None,

            ast::TopDecl::Import(_) => panic!(), // imports should've been resolved at this point
        })
        .collect()
}
