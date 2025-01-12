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
        param_ty.node.fvs_(&mut fvs);
    }
    if let Some(ret) = &decl.sig.return_ty {
        ret.node.fvs_(&mut fvs);
    }

    for fv in fvs.difference(bound_vars) {
        if !decl
            .sig
            .type_params
            .iter()
            .any(|ty_param| ty_param.id.node == *fv)
        {
            decl.sig.type_params.push(ast::TypeParam {
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
    decl.ty.node.fvs_(&mut impl_context_fvs);
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
                add_missing_type_params_fun(fun_decl, &impl_context_vars);
            }
        }
    }
}
