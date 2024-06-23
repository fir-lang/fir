use crate::interpreter::*;

pub fn collect_types(pgm: &[L<ast::TopDecl>]) -> (Map<SmolStr, TyCon>, u64) {
    let mut ty_cons: Map<SmolStr, TyCon> = Default::default();

    ty_cons.insert(
        SmolStr::new("Bool"),
        TyCon {
            value_constrs: vec![
                ValCon {
                    name: Some(SmolStr::new("False")),
                    fields: Fields::Unnamed(0),
                },
                ValCon {
                    name: Some(SmolStr::new("True")),
                    fields: Fields::Unnamed(0),
                },
            ],
            type_tag: FALSE_TYPE_TAG,
        },
    );

    ty_cons.insert(
        SmolStr::new("I32"),
        TyCon {
            value_constrs: vec![],
            type_tag: I32_TYPE_TAG,
        },
    );

    ty_cons.insert(
        SmolStr::new("Str"),
        TyCon {
            value_constrs: vec![],
            type_tag: STR_TYPE_TAG,
        },
    );

    ty_cons.insert(
        SmolStr::new("StrView"),
        TyCon {
            value_constrs: vec![],
            type_tag: STR_VIEW_TYPE_TAG,
        },
    );

    ty_cons.insert(
        SmolStr::new("Array"),
        TyCon {
            value_constrs: vec![],
            type_tag: ARRAY_TYPE_TAG,
        },
    );

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
        } = match &decl.thing {
            ast::TopDecl::Type(ty_decl) => &ty_decl.thing,
            ast::TopDecl::Fun(_) => continue,
        };

        match rhs {
            ast::TypeDeclRhs::Sum(named_constrs) => {
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
                assert!(old.is_none());
                next_type_tag += named_constrs.len() as u64;
            }

            ast::TypeDeclRhs::Product(fields) => {
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
            "__sub" => BuiltinFun::I32Sub,
            "__cmp" => BuiltinFun::I32Cmp,
            "__eq" => BuiltinFun::I32Eq,
            "toStr" => BuiltinFun::I32ToStr,
        },
        "Bool" => {
            "__and" => BuiltinFun::BoolAnd,
            "__or" => BuiltinFun::BoolOr,
            "toStr" => BuiltinFun::BoolToStr,
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

    let mut associated_fun_indices: Map<SmolStr, u64> = Default::default();

    for decl in pgm {
        let fun_decl: ast::FunDecl = match decl.thing {
            ast::TopDecl::Type(_) => continue,
            ast::TopDecl::Fun(fun_decl) => fun_decl.thing,
        };

        let old = match &fun_decl.type_name {
            Some(type_name) => {
                let idx_entry = associated_fun_indices.entry(type_name.clone()).or_insert(0);
                let idx = *idx_entry;
                *idx_entry += 1;
                associated_funs
                    .entry(type_name.clone())
                    .or_default()
                    .insert(
                        fun_decl.name.clone(),
                        Fun {
                            idx,
                            kind: FunKind::Source(fun_decl),
                        },
                    )
            }

            None => {
                let idx = top_level_funs.len() as u64;
                top_level_funs.insert(
                    fun_decl.name.clone(),
                    Fun {
                        idx,
                        kind: FunKind::Source(fun_decl),
                    },
                )
            }
        };

        assert!(old.is_none());
    }

    (top_level_funs, associated_funs)
}
