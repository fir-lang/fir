use crate::ast;
use crate::collections::Set;
use crate::type_checker::Id;

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
                add_missing_type_params_fun(&mut decl.node.sig, &Default::default())
            }

            ast::TopDecl::Impl(decl) => add_missing_type_params_impl(&mut decl.node),

            ast::TopDecl::Trait(decl) => add_missing_type_params_trait(&mut decl.node),

            ast::TopDecl::Type(_) | ast::TopDecl::Import(_) => {}
        }
    }
}

fn add_missing_type_params_fun(sig: &mut ast::FunSig, bound_vars: &Set<Id>) {
    let mut fvs: Set<Id> = Default::default();
    match &sig.self_ {
        ast::SelfParam::No | ast::SelfParam::Inferred => {}
        ast::SelfParam::Explicit(ty) => collect_fvs(ty, &mut fvs),
    }
    for (_, param_ty) in &sig.params {
        collect_fvs(&param_ty.node, &mut fvs);
    }
    if let Some(exn) = &sig.exceptions {
        collect_fvs(&exn.node, &mut fvs);
    }
    if let Some(ret) = &sig.return_ty {
        collect_fvs(&ret.node, &mut fvs);
    }

    for fv in fvs.difference(bound_vars) {
        if !sig
            .type_params
            .iter()
            .any(|ty_param| ty_param.id.node == *fv)
        {
            sig.type_params.push(ast::TypeParam {
                id: ast::L {
                    node: fv.clone(),
                    loc: ast::Loc::dummy(),
                },
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
        decl.context.push(ast::TypeParam {
            id: ast::L {
                node: fv.clone(),
                loc: ast::Loc::dummy(),
            },
            bounds: vec![],
        });
    }

    // Add missing parameters to functions in the `impl` block.
    impl_context_vars.extend(impl_context_fvs);
    for item in &mut decl.items {
        match &mut item.node {
            ast::ImplDeclItem::AssocTy(_) => {}
            ast::ImplDeclItem::Fun(fun_decl) => {
                add_missing_type_params_fun(&mut fun_decl.sig, &impl_context_vars);
            }
        }
    }
}

fn add_missing_type_params_trait(decl: &mut ast::TraitDecl) {
    let trait_context_vars: Set<Id> = [decl.ty.id.node.clone()].into_iter().collect();
    for item in &mut decl.items {
        match &mut item.node {
            ast::TraitDeclItem::AssocTy(_) => {}
            ast::TraitDeclItem::Fun(fun_decl) => {
                add_missing_type_params_fun(&mut fun_decl.sig, &trait_context_vars);
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

        ast::Type::Fn(ast::FnType {
            args,
            ret,
            exceptions,
        }) => {
            for arg in args {
                collect_fvs(&arg.node, fvs);
            }
            if let Some(ret) = ret {
                collect_fvs(&ret.node, fvs);
            }
            if let Some(exn) = exceptions {
                collect_fvs(&exn.node, fvs);
            }
        }
    }
}
