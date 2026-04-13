use crate::ast;

use super::*;

/// Generate an `impl ToDoc[TypeName[...]]` for the given type declaration.
pub fn derive_to_doc(type_decl: &ast::TypeDecl, loc: &ast::Loc) -> ast::L<ast::TopDecl> {
    let self_ty = type_with_params(loc, &type_decl.name, &type_decl.type_params);
    let doc_ty = l(
        loc,
        ast::Type::Named(ast::NamedType {
            mod_prefix: None,
            name: ast::Name::new_static("Doc"),
            args: vec![],
        }),
    );

    let body = match &type_decl.rhs {
        None => derive_to_doc_empty_product(loc, &type_decl.name),
        Some(ast::TypeDeclRhs::Product(fields)) => {
            derive_to_doc_product(loc, &type_decl.name, fields)
        }
        Some(ast::TypeDeclRhs::Sum { cons, .. }) => derive_to_doc_sum(loc, &type_decl.name, cons),
        Some(ast::TypeDeclRhs::Synonym(_)) => unreachable!("Caught in expand_derives"),
    };

    let fun = make_method(loc, "toDoc", self_ty, vec![], doc_ty, body);

    make_impl_top_decl(loc, "ToDoc", type_decl, fun)
}

/// Derive ToDoc for a product type with fields.
fn derive_to_doc_product(
    loc: &ast::Loc,
    type_name: &ast::Name,
    fields: &ast::ConFields,
) -> Vec<ast::L<ast::Stmt>> {
    match fields {
        ast::ConFields::Empty => derive_to_doc_empty_product(loc, type_name),

        ast::ConFields::Named {
            fields: named_fields,
            extension,
        } => {
            let mut stmts = vec![];

            let ext_expr = if extension.is_some() {
                let names: Vec<ast::Name> =
                    named_fields.iter().map(|(name, _)| name.clone()).collect();
                stmts.push(let_destructure_rest(
                    loc,
                    type_name,
                    &names,
                    "exts",
                    var(loc, "self"),
                ));
                Some(var(loc, "exts"))
            } else {
                None
            };

            stmts.extend(gen_named_field_args(
                loc,
                named_fields,
                &|loc, field_name| field_sel(loc, var(loc, "self"), field_name),
                ext_expr,
            ));

            // Doc.grouped(Doc.str("TypeName") + Doc.char('(') + args)
            let result = doc_grouped(
                loc,
                add(
                    loc,
                    add(loc, doc_str(loc, type_name.as_str()), doc_char(loc, '(')),
                    var(loc, "args"),
                ),
            );
            stmts.push(l(loc, ast::Stmt::Expr(result.node)));
            stmts
        }

        ast::ConFields::Unnamed { fields } => {
            let mut stmts = gen_unnamed_field_args(loc, fields.len());

            // Doc.grouped(Doc.str("TypeName") + Doc.char('(') + args)
            let result = doc_grouped(
                loc,
                add(
                    loc,
                    add(loc, doc_str(loc, type_name.as_str()), doc_char(loc, '(')),
                    var(loc, "args"),
                ),
            );
            stmts.push(l(loc, ast::Stmt::Expr(result.node)));
            stmts
        }
    }
}

/// Derive ToDoc for an empty product type (no fields).
///
/// For empty product, just output `Doc.str("TypeName")`
fn derive_to_doc_empty_product(loc: &ast::Loc, type_name: &ast::Name) -> Vec<ast::L<ast::Stmt>> {
    vec![l(
        loc,
        ast::Stmt::Expr(doc_str(loc, type_name.as_str()).node),
    )]
}

/// Derive ToDoc for a sum type.
fn derive_to_doc_sum(
    loc: &ast::Loc,
    type_name: &ast::Name,
    cons: &[ast::ConDecl],
) -> Vec<ast::L<ast::Stmt>> {
    let mut alts: Vec<ast::Alt> = Vec::new();

    for con in cons {
        let con_name_str = format!("{}.{}", type_name, con.name);

        // Build pattern and body based on field type
        let (pat_fields, rest_pat, body) = match &con.fields {
            ast::ConFields::Empty => {
                // Pattern: TypeName.ConName (no fields)
                // Body: Doc.str("TypeName.ConName")
                let body = vec![l(loc, ast::Stmt::Expr(doc_str(loc, &con_name_str).node))];
                (vec![], ast::RestPat::No, body)
            }

            ast::ConFields::Named {
                fields: named_fields,
                extension,
            } => {
                // Pattern: TypeName.ConName(field1, field2, ..exts)
                let pat_fields: Vec<ast::Named<ast::L<ast::Pat>>> = named_fields
                    .iter()
                    .map(|(name, _)| ast::Named {
                        name: Some(name.clone()),
                        node: l(
                            loc,
                            ast::Pat::Var(ast::VarPat {
                                var: name.clone(),
                                ty: None,
                                refined: None,
                            }),
                        ),
                    })
                    .collect();

                let rest_pat = if extension.is_some() {
                    ast::RestPat::Bind(ast::VarPat {
                        var: ast::Name::new_static("exts"),
                        ty: None,
                        refined: None,
                    })
                } else {
                    ast::RestPat::No
                };

                let ext_expr = if extension.is_some() {
                    Some(var(loc, "exts"))
                } else {
                    None
                };

                let mut body = gen_named_field_args(
                    loc,
                    named_fields,
                    &|loc, field_name| var(loc, field_name),
                    ext_expr,
                );

                // Doc.grouped(Doc.str("TypeName.ConName") + Doc.char('(') + args)
                let result = doc_grouped(
                    loc,
                    add(
                        loc,
                        add(loc, doc_str(loc, &con_name_str), doc_char(loc, '(')),
                        var(loc, "args"),
                    ),
                );
                body.push(l(loc, ast::Stmt::Expr(result.node)));

                (pat_fields, rest_pat, body)
            }

            ast::ConFields::Unnamed { fields } => {
                // Pattern: TypeName.ConName(i0, i1, ...)
                let pat_fields: Vec<ast::Named<ast::L<ast::Pat>>> = (0..fields.len())
                    .map(|i| ast::Named {
                        name: None,
                        node: l(
                            loc,
                            ast::Pat::Var(ast::VarPat {
                                var: ast::Name::new(format!("i{}", i)),
                                ty: None,
                                refined: None,
                            }),
                        ),
                    })
                    .collect();

                let mut body = gen_unnamed_field_args(loc, fields.len());

                // Doc.grouped(Doc.str("TypeName.ConName") + Doc.char('(') + args)
                let result = doc_grouped(
                    loc,
                    add(
                        loc,
                        add(loc, doc_str(loc, &con_name_str), doc_char(loc, '(')),
                        var(loc, "args"),
                    ),
                );
                body.push(l(loc, ast::Stmt::Expr(result.node)));

                (pat_fields, ast::RestPat::No, body)
            }
        };

        let con_pat = l(
            loc,
            ast::Pat::Con(ast::ConPat {
                con: ast::Con {
                    mod_prefix: None,
                    ty: type_name.clone(),
                    con: Some(con.name.clone()),
                    user_ty_args: vec![],
                    ty_args: vec![],
                    inferred_ty: None,
                },
                fields: pat_fields,
                rest: rest_pat,
            }),
        );

        alts.push(ast::Alt {
            pat: con_pat,
            guard: None,
            rhs: body,
        });
    }

    let match_expr = ast::Expr::Match(ast::MatchExpr {
        scrutinee: Box::new(var(loc, "self")),
        alts,
        inferred_ty: None,
    });

    vec![l(loc, ast::Stmt::Expr(match_expr))]
}

/// Generate the args-building statements for named fields, using a given accessor function to get
/// each field value.
///
/// `accessor` takes (loc, field_name) and returns the expression for that field's value.
///
/// If `ext_expr` is provided, it is appended after the named fields (with a comma separator if
/// there are named fields).
fn gen_named_field_args(
    loc: &ast::Loc,
    fields: &[(ast::Name, ast::L<ast::Type>)],
    accessor: &dyn Fn(&ast::Loc, &ast::Name) -> ast::L<ast::Expr>,
    ext_expr: Option<ast::L<ast::Expr>>,
) -> Vec<ast::L<ast::Stmt>> {
    let mut stmts = vec![];

    // let args = Doc.break_(0)
    stmts.push(let_stmt(loc, "args", doc_break(loc, 0)));

    for (i, (field_name, _)) in fields.iter().enumerate() {
        if i != 0 {
            // args += Doc.char(',') + Doc.break_(1)
            stmts.push(plus_eq_stmt(
                loc,
                "args",
                add(loc, doc_char(loc, ','), doc_break(loc, 1)),
            ));
        }

        // args += Doc.grouped(Doc.str("fieldName =") + Doc.nested(4, Doc.break_(1) + <accessor>.toDoc()))
        let field_val = accessor(loc, field_name);
        let to_doc_call = method_call(loc, field_val, "toDoc", vec![]);
        let nested = doc_nested(loc, 4, add(loc, doc_break(loc, 1), to_doc_call));
        let grouped = doc_grouped(
            loc,
            add(loc, doc_str(loc, &format!("{} =", field_name)), nested),
        );
        stmts.push(plus_eq_stmt(loc, "args", grouped));
    }

    if let Some(ext) = ext_expr {
        if !fields.is_empty() {
            // args += Doc.char(',') + Doc.break_(1)
            stmts.push(plus_eq_stmt(
                loc,
                "args",
                add(loc, doc_char(loc, ','), doc_break(loc, 1)),
            ));
        }
        // args += ext.toDoc()
        let to_doc_call = method_call(loc, ext, "toDoc", vec![]);
        stmts.push(plus_eq_stmt(loc, "args", to_doc_call));
    }

    // args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
    let nest_group = method_call(
        loc,
        method_call(loc, var(loc, "args"), "nest", vec![u32_lit(loc, 4)]),
        "group",
        vec![],
    );
    let rhs = add(
        loc,
        add(loc, nest_group, doc_break(loc, 0)),
        doc_char(loc, ')'),
    );
    stmts.push(assign_stmt(loc, "args", rhs));

    stmts
}

/// Generate the args-building statements for unnamed fields, using bound variables `i0`, `i1`, ...
fn gen_unnamed_field_args(loc: &ast::Loc, num_fields: usize) -> Vec<ast::L<ast::Stmt>> {
    let mut stmts = vec![];

    // let args = Doc.break_(0)
    stmts.push(let_stmt(loc, "args", doc_break(loc, 0)));

    for i in 0..num_fields {
        if i != 0 {
            // args += Doc.char(',') + Doc.break_(1)
            stmts.push(plus_eq_stmt(
                loc,
                "args",
                add(loc, doc_char(loc, ','), doc_break(loc, 1)),
            ));
        }

        // args += i<N>.toDoc()
        let to_doc_call = method_call(loc, var(loc, &format!("i{}", i)), "toDoc", vec![]);
        stmts.push(plus_eq_stmt(loc, "args", to_doc_call));
    }

    // args = args.nest(4).group() + Doc.break_(0) + Doc.char(')')
    let nest_group = method_call(
        loc,
        method_call(loc, var(loc, "args"), "nest", vec![u32_lit(loc, 4)]),
        "group",
        vec![],
    );
    let rhs = add(
        loc,
        add(loc, nest_group, doc_break(loc, 0)),
        doc_char(loc, ')'),
    );
    stmts.push(assign_stmt(loc, "args", rhs));

    stmts
}

// Doc.str("...")
fn doc_str(loc: &ast::Loc, s: &str) -> ast::L<ast::Expr> {
    assoc_fn_call(loc, "Doc", "str", vec![str_lit(loc, s)])
}

// Doc.char(c)
fn doc_char(loc: &ast::Loc, c: char) -> ast::L<ast::Expr> {
    assoc_fn_call(loc, "Doc", "char", vec![char_lit(loc, c)])
}

// Doc.break_(n)
fn doc_break(loc: &ast::Loc, n: u32) -> ast::L<ast::Expr> {
    assoc_fn_call(loc, "Doc", "break_", vec![u32_lit(loc, n)])
}

// Doc.nested(n, expr)
fn doc_nested(loc: &ast::Loc, n: u32, expr: ast::L<ast::Expr>) -> ast::L<ast::Expr> {
    assoc_fn_call(loc, "Doc", "nested", vec![u32_lit(loc, n), expr])
}

// Doc.grouped(expr)
fn doc_grouped(loc: &ast::Loc, expr: ast::L<ast::Expr>) -> ast::L<ast::Expr> {
    assoc_fn_call(loc, "Doc", "grouped", vec![expr])
}
