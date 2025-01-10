use crate::ast;
use crate::collections::{Map, Set};
use crate::type_checker::unification::unify;
use crate::type_checker::{FunArgs, Id, Kind, Ty, TyVarGen};
use crate::utils::loc_display;

use smol_str::SmolStr;

/*
We allow omitting type parameters in these contexts:

- Top-level functions: `t` in

    fn f1[t](a: t)
        ...

- Associated functions: same as above, but in an associated function:

    impl T:
        fn f1[t](self, a: t)
            ...

- Impl blocks:

    impl T[x]:
        ...

For now we modify the AST nodes to add missing type parameters.
*/
pub fn add_missing_type_params(pgm: &mut ast::Module) {
    for decl in pgm {
        match &mut decl.node {
            ast::TopDecl::Fun(decl) => {
                add_missing_type_params_fun(&mut decl.node, &Default::default())
            }

            ast::TopDecl::Impl(decl) => add_missing_type_params_impl(&mut decl.node),

            ast::TopDecl::Type(_) | ast::TopDecl::Import(_) | ast::TopDecl::Trait(_) => {}
        }
    }
}

fn add_missing_type_params_fun(decl: &mut ast::FunDecl, bound_vars: &Set<Id>) {
    let mut fvs: Set<Id> = Default::default();
    for (_, param_ty) in &decl.sig.params {
        collect_fvs(&param_ty.node, &mut fvs);
    }
    if let Some(ret) = &decl.sig.return_ty {
        collect_fvs(&ret.node, &mut fvs);
    }

    for fv in fvs.difference(bound_vars) {
        if !decl
            .sig
            .type_params
            .iter()
            .any(|ty_param| ty_param.id.node == *fv)
        {
            decl.sig.type_params.push(ast::TypeParamWithBounds {
                id: ast::L {
                    node: fv.clone(),
                    loc: ast::Loc::dummy(),
                },
                kind: None,
                bounds: vec![],
            });
        }
    }
}

fn add_missing_type_params_impl(decl: &mut ast::ImplDecl) {
    let mut impl_context_vars: Set<Id> = decl
        .context
        .iter()
        .map(|param| param.id.node.clone())
        .collect();

    // Add missing parameters to the `impl` block context.
    let mut impl_context_fvs: Set<Id> = Default::default();
    collect_fvs(&decl.ty.node, &mut impl_context_fvs);
    for fv in impl_context_fvs.difference(&impl_context_vars) {
        decl.context.push(ast::TypeParamWithBounds {
            id: ast::L {
                node: fv.clone(),
                loc: ast::Loc::dummy(),
            },
            kind: None,
            bounds: vec![],
        });
    }

    // Add missing parameters to functions in the `impl` block.
    impl_context_vars.extend(impl_context_fvs);
    for item in &mut decl.items {
        match &mut item.node {
            ast::ImplDeclItem::AssocTy(_) => {}
            ast::ImplDeclItem::Fun(fun_decl) => {
                add_missing_type_params_fun(fun_decl, &impl_context_vars);
            }
        }
    }
}

fn collect_fvs(ty: &ast::Type, fvs: &mut Set<Id>) {
    match ty {
        ast::Type::Named(ast::NamedType { name: _, args }) => {
            for arg in args {
                collect_fvs(&arg.node.1.node, fvs);
            }
        }

        ast::Type::Var(var) => {
            fvs.insert(var.clone());
        }

        ast::Type::Record { fields, extension } => {
            for field in fields {
                collect_fvs(&field.node, fvs);
            }
            if let Some(ext) = extension {
                fvs.insert(ext.clone());
            }
        }

        ast::Type::Variant { alts, extension } => {
            for alt in alts {
                for field in &alt.fields {
                    collect_fvs(&field.node, fvs);
                }
            }
            if let Some(ext) = extension {
                fvs.insert(ext.clone());
            }
        }

        ast::Type::Fn(ast::FnType { args, ret }) => {
            for arg in args {
                collect_fvs(&arg.node, fvs);
            }
            if let Some(ret) = ret {
                collect_fvs(&ret.node, fvs);
            }
        }
    }
}

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
#[allow(unused)]
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

            ast::TopDecl::Fun(decl) => {}

            ast::TopDecl::Trait(l) => todo!(),

            ast::TopDecl::Impl(l) => todo!(),

            ast::TopDecl::Import(_) => {}
        }
    }
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
