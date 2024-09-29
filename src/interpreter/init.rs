use crate::interpreter::*;
use crate::utils::loc_display;

pub fn collect_types(pgm: &[L<ast::TopDecl>]) -> (Map<Id, TyCon>, u64) {
    let mut ty_cons: Map<Id, TyCon> = Default::default();

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

    ty_cons.insert(
        SmolStr::new("#METHOD"),
        TyCon {
            value_constrs: vec![],
            type_tag: METHOD_TYPE_TAG,
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

pub fn collect_funs(pgm: Vec<L<ast::TopDecl>>) -> (Map<Id, Fun>, Map<Id, Map<Id, Fun>>) {
    macro_rules! builtin_top_level_funs {
        ($($fname:expr => $fkind:expr),* $(,)?) => {{
            let mut map: Map<Id, Fun> = Default::default();
            #[allow(unused_assignments)] // idx is not read after the last increment
            {
                let mut idx = 0;
                $(
                    map.insert(Id::new($fname), Fun { idx, kind: FunKind::Builtin($fkind) });
                    idx += 1;
                )*
            }
            map
        }};
    }

    let mut top_level_funs: Map<Id, Fun> = builtin_top_level_funs! {
        "print" => BuiltinFun::Print,
        "printStr" => BuiltinFun::PrintStr,
        "panic@Ptr" => BuiltinFun::Panic,
    };

    macro_rules! builtin_associated_funs {
        ($($type:expr => {$($fname:expr => $fkind:expr),* $(,)?}),* $(,)?) => {{
            let mut map: Map<Id, Map<Id, Fun>> = Default::default();
            #[allow(unused_assignments)] // idx is not read after the last increment
            {
                $(
                    let mut fun_map: Map<Id, Fun> = Default::default();
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

    let mut associated_funs: Map<Id, Map<Id, Fun>> = builtin_associated_funs! {
        "I32" => {
            "__add" => BuiltinFun::I32Add,
            "cmp" => BuiltinFun::I32Cmp,
            "__mul" => BuiltinFun::I32Mul,
            "__sub" => BuiltinFun::I32Sub,
            "__eq" => BuiltinFun::I32Eq,
            "__bitand" => BuiltinFun::I32BitAnd,
            "__bitor" => BuiltinFun::I32BitOr,
            "toStr" => BuiltinFun::I32ToStr,
            "__shl" => BuiltinFun::I32Shl,
            "__shr" => BuiltinFun::I32Shr,
        },
        "U32" => {
            "__add" => BuiltinFun::U32Add,
            "cmp" => BuiltinFun::U32Cmp,
            "__mul" => BuiltinFun::U32Mul,
            "__sub" => BuiltinFun::U32Sub,
            "__eq" => BuiltinFun::U32Eq,
            "__bitand" => BuiltinFun::U32BitAnd,
            "__bitor" => BuiltinFun::U32BitOr,
            "toStr" => BuiltinFun::U32ToStr,
            "__shl" => BuiltinFun::U32Shl,
            "__shr" => BuiltinFun::U32Shr,
        },
        "I8" => {
            "__add" => BuiltinFun::I8Add,
            "cmp" => BuiltinFun::I8Cmp,
            "__mul" => BuiltinFun::I8Mul,
            "__sub" => BuiltinFun::I8Sub,
            "__eq" => BuiltinFun::I8Eq,
            "__bitand" => BuiltinFun::I8BitAnd,
            "__bitor" => BuiltinFun::I8BitOr,
            "toStr" => BuiltinFun::I8ToStr,
            "__shl" => BuiltinFun::I8Shl,
            "__shr" => BuiltinFun::I8Shr,
        },
        "U8" => {
            "__add" => BuiltinFun::U8Add,
            "cmp" => BuiltinFun::U8Cmp,
            "__mul" => BuiltinFun::U8Mul,
            "__sub" => BuiltinFun::U8Sub,
            "__eq" => BuiltinFun::U8Eq,
            "__bitand" => BuiltinFun::U8BitAnd,
            "__bitor" => BuiltinFun::U8BitOr,
            "toStr" => BuiltinFun::U8ToStr,
            "__shl" => BuiltinFun::U8Shl,
            "__shr" => BuiltinFun::U8Shr,
        },
        "Array@U8" => {
            "new" => BuiltinFun::ArrayU8New,
            "len" => BuiltinFun::ArrayU8Len,
            "set" => BuiltinFun::ArrayU8Set,
            "get" => BuiltinFun::ArrayU8Get,
        },
        "Array@I8" => {
            "new" => BuiltinFun::ArrayI8New,
            "len" => BuiltinFun::ArrayI8Len,
            "set" => BuiltinFun::ArrayI8Set,
            "get" => BuiltinFun::ArrayI8Get,
        },
        "Array@U32" => {
            "new" => BuiltinFun::ArrayU32New,
            "len" => BuiltinFun::ArrayU32Len,
            "set" => BuiltinFun::ArrayU32Set,
            "get" => BuiltinFun::ArrayU32Get,
        },
        "Array@I32" => {
            "new" => BuiltinFun::ArrayI32New,
            "len" => BuiltinFun::ArrayI32Len,
            "set" => BuiltinFun::ArrayI32Set,
            "get" => BuiltinFun::ArrayI32Get,
        },
        "Array@Ptr" => {
            "new" => BuiltinFun::ArrayPtrNew,
            "len" => BuiltinFun::ArrayPtrLen,
            "set" => BuiltinFun::ArrayPtrSet,
            "get" => BuiltinFun::ArrayPtrGet,
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
                let implementing_ty = match &impl_decl.node.ty.node {
                    ast::Type::Named(ast::NamedType { name, args: _ }) => name,
                    ast::Type::Record(_) => {
                        panic!(
                            "{}: Impl block for record type",
                            loc_display(&impl_decl.loc)
                        )
                    }
                };

                for item in impl_decl.node.items {
                    let fun_decl = match item.node {
                        ast::ImplDeclItem::AssocTy(_) => continue,
                        ast::ImplDeclItem::Fun(fun) => fun,
                    };

                    if fun_decl.body.is_none() {
                        // Built-in function, should be added above.
                        continue;
                    }

                    let fun_map = associated_funs.entry(implementing_ty.clone()).or_default();
                    let fun_idx = fun_map.len();
                    fun_map.insert(
                        fun_decl.sig.name.node.clone(),
                        Fun {
                            idx: fun_idx as u64,
                            kind: FunKind::Source(fun_decl),
                        },
                    );
                }
            }
        }
    }

    (top_level_funs, associated_funs)
}
