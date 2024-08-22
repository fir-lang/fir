use crate::{interpreter::*, type_checker::convert_ast_ty};

pub fn collect_types(pgm: &[L<ast::TopDecl>]) -> (Map<SmolStr, TyCon>, u64) {
    let mut ty_cons: Map<SmolStr, TyCon> = Default::default();

    ty_cons.insert(
        SmolStr::new("#CONSTR"),
        TyCon {
            value_constrs: vec![],
            type_tag: CONSTR_TYPE_TAG,
        },
    );

    ty_cons.insert(
        SmolStr::new("#TOP_FUN"),
        TyCon {
            value_constrs: vec![],
            type_tag: TOP_FUN_TYPE_TAG,
        },
    );

    ty_cons.insert(
        SmolStr::new("#ASSOC_FUN"),
        TyCon {
            value_constrs: vec![],
            type_tag: ASSOC_FUN_TYPE_TAG,
        },
    );

    let mut next_type_tag = FIRST_TYPE_TAG;

    fn convert_constr_fields(fields: &ast::ConstructorFields) -> Fields {
        match fields {
            ast::ConstructorFields::Empty => Fields::Unnamed(0),

            ast::ConstructorFields::Named(named_fields) => {
                assert!(!named_fields.is_empty());
                Fields::Named(named_fields.iter().map(|(name, _)| name.clone()).collect())
            }

            ast::ConstructorFields::Unnamed(tys) => {
                assert!(!tys.is_empty());
                Fields::Unnamed(tys.len() as u32)
            }
        }
    }

    for decl in pgm {
        let ast::TypeDecl {
            name,
            type_params: _,
            rhs,
        } = match &decl.node {
            ast::TopDecl::Type(ty_decl) => &ty_decl.node,
            ast::TopDecl::Import(_) => panic!("Import declaration in the interpreter"),
            ast::TopDecl::Fun(_) | ast::TopDecl::Trait(_) | ast::TopDecl::Impl(_) => continue,
        };

        match rhs {
            None => {
                ty_cons.insert(
                    name.clone(),
                    TyCon {
                        value_constrs: vec![],
                        type_tag: next_type_tag,
                    },
                );
                next_type_tag += 1;
            }

            Some(ast::TypeDeclRhs::Sum(named_constrs)) => {
                let mut constrs: Vec<ValCon> = Vec::with_capacity(named_constrs.len());
                for ast::ConstructorDecl {
                    name: constr_name,
                    fields,
                } in named_constrs
                {
                    constrs.push(ValCon {
                        name: Some(constr_name.clone()),
                        fields: convert_constr_fields(fields),
                    });
                }
                let old = ty_cons.insert(
                    name.clone(),
                    TyCon {
                        value_constrs: constrs,
                        type_tag: next_type_tag,
                    },
                );
                assert!(
                    old.is_none(),
                    "Type constructor {} defined multiple times",
                    name
                );
                next_type_tag += named_constrs.len() as u64;
            }

            Some(ast::TypeDeclRhs::Product(fields)) => {
                let constrs: Vec<ValCon> = vec![ValCon {
                    name: Some(name.clone()),
                    fields: convert_constr_fields(fields),
                }];
                ty_cons.insert(
                    name.clone(),
                    TyCon {
                        value_constrs: constrs,
                        type_tag: next_type_tag,
                    },
                );
                next_type_tag += 1;
            }
        }
    }

    (ty_cons, next_type_tag)
}

pub fn collect_funs(
    pgm: Vec<L<ast::TopDecl>>,
    tys: &PgmTypes,
) -> (Map<SmolStr, Fun>, Map<SmolStr, Map<SmolStr, Fun>>) {
    macro_rules! builtin_top_level_funs {
        ($($fname:expr => $fkind:expr),* $(,)?) => {{
            let mut map: Map<SmolStr, Fun> = Default::default();
            #[allow(unused_assignments)] // idx is not read after the last increment
            {
                let mut idx = 0;
                $(
                    map.insert(SmolStr::new($fname), Fun { idx, kind: FunKind::Builtin($fkind) });
                    idx += 1;
                )*
            }
            map
        }};
    }

    let mut top_level_funs: Map<SmolStr, Fun> = builtin_top_level_funs! {
        "print" => BuiltinFun::Print,
        "printStr" => BuiltinFun::PrintStr,
        "printStrView" => BuiltinFun::PrintStrView,
        "panic" => BuiltinFun::Panic,
    };

    macro_rules! builtin_associated_funs {
        ($($type:expr => {$($fname:expr => $fkind:expr),* $(,)?}),* $(,)?) => {{
            let mut map: Map<SmolStr, Map<SmolStr, Fun>> = Default::default();
            #[allow(unused_assignments)] // idx is not read after the last increment
            {
                $(
                    let mut fun_map: Map<SmolStr, Fun> = Default::default();
                    let mut idx = 0;
                    $(
                        fun_map.insert(SmolStr::new($fname), Fun { idx, kind: FunKind::Builtin($fkind) });
                        idx += 1;
                    )*
                    map.insert(SmolStr::new($type), fun_map);
                )*
            }
            map
        }};
    }

    let mut associated_funs: Map<SmolStr, Map<SmolStr, Fun>> = builtin_associated_funs! {
        "Str" => {
            "len" => BuiltinFun::StrLen,
            "__eq" => BuiltinFun::StrEq,
            "substr" => BuiltinFun::StrSubstr,
        },
        "I32" => {
            "__add" => BuiltinFun::I32Add,
            "__cmp" => BuiltinFun::I32Cmp,
            "__mul" => BuiltinFun::I32Mul,
            "__sub" => BuiltinFun::I32Sub,
            "__eq" => BuiltinFun::I32Eq,
            "toStr" => BuiltinFun::I32ToStr,
        },
        "StrView" => {
            "__eq" => BuiltinFun::StrViewEq,
            "substr" => BuiltinFun::StrViewSubstr,
            "len" => BuiltinFun::StrViewLen,
            "startsWith" => BuiltinFun::StrViewStartsWith,
            "isEmpty" => BuiltinFun::StrViewIsEmpty,
            "toStr" => BuiltinFun::StrViewToStr,
        },
        "Array" => {
            "new" => BuiltinFun::ArrayNew,
            "len" => BuiltinFun::ArrayLen,
            "set" => BuiltinFun::ArraySet,
            "get" => BuiltinFun::ArrayGet,
        },
    };

    for decl in pgm {
        match decl.node {
            ast::TopDecl::Type(_) | ast::TopDecl::Trait(_) => continue,

            ast::TopDecl::Import(_) => panic!("Import declaration in the interpreter"),

            ast::TopDecl::Fun(fun_decl) => {
                if fun_decl.node.body.is_none() {
                    // Built-in function, should be added above.
                    continue;
                }

                let idx = top_level_funs.len() as u64;
                top_level_funs.insert(
                    fun_decl.node.sig.name.node.clone(),
                    Fun {
                        idx,
                        kind: FunKind::Source(fun_decl.node),
                    },
                );
            }

            ast::TopDecl::Impl(impl_decl) => {
                let ast_ty: &ast::Type = &impl_decl.node.ty.node;
                let ty_vars: Set<Id> = impl_decl
                    .node
                    .context
                    .iter()
                    .map(|ty| ty.node.0.clone())
                    .collect();
                let ty = convert_ast_ty(&tys.cons, &ty_vars, ast_ty, &impl_decl.node.ty.loc);

                // method_ty = type to add the method to.
                let (mut method_ty, args) = ty.con().unwrap();
                if tys.cons.get(&method_ty).unwrap().is_trait() {
                    assert_eq!(args.len(), 1);
                    let ty = &args[0];
                    let (ty_con, _) = ty.con().unwrap();
                    method_ty = ty_con;
                }

                for item in impl_decl.node.items {
                    let fun_decl = match item.node {
                        ast::ImplDeclItem::AssocTy(_) => continue,
                        ast::ImplDeclItem::Fun(fun) => fun,
                    };

                    if fun_decl.body.is_none() {
                        // Built-in function, should be added above.
                        continue;
                    }

                    associated_funs
                        .entry(method_ty.clone())
                        .or_default()
                        .insert(
                            fun_decl.sig.name.node.clone(),
                            Fun {
                                idx: 0, // TODO: Is this used?
                                kind: FunKind::Source(fun_decl),
                            },
                        );
                }
            }
        }
    }

    (top_level_funs, associated_funs)
}
