use crate::ast;

use super::*;

/// Generate an `impl Eq[TypeName[...]]` for the given type declaration.
pub fn derive_eq(type_decl: &ast::TypeDecl, loc: &ast::Loc) -> ast::L<ast::TopDecl> {
    let self_ty = type_with_params(loc, &type_decl.name, &type_decl.type_params);

    let bool_ty = l(
        loc,
        ast::Type::Named(ast::NamedType {
            mod_prefix: None,
            name: ast::Name::new_static("Bool"),
            args: vec![],
        }),
    );

    let body = match &type_decl.rhs {
        None => {
            // Empty product type (no fields): `Bool.True`
            vec![l(
                loc,
                ast::Stmt::Expr(con_sel(loc, "Bool", Some("True")).node),
            )]
        }
        Some(ast::TypeDeclRhs::Product(fields)) => derive_eq_product(loc, &type_decl.name, fields),
        Some(ast::TypeDeclRhs::Sum { cons, .. }) => derive_eq_sum(loc, &type_decl.name, cons),
        Some(ast::TypeDeclRhs::Synonym(_)) => {
            // Should be caught at the call site.
            panic!("BUG: Type synonym in derive(Eq) macro")
        }
    };

    let fun = make_method(
        loc,
        "__eq",
        self_ty.clone(),
        vec![(ast::Name::new_static("other"), self_ty)],
        bool_ty,
        body,
    );

    make_impl_top_decl(loc, "Eq", type_decl, fun)
}

/// Generate Eq body for a product type.
///
/// For named fields: `self.field1 == other.field1 && self.field2 == other.field2 && ...`
/// For unnamed fields: `self._0 == other._0 && self._1 == other._1 && ...`
/// For empty: `Bool.True`
fn derive_eq_product(
    loc: &ast::Loc,
    type_name: &ast::Name,
    fields: &ast::ConFields,
) -> Vec<ast::L<ast::Stmt>> {
    match fields {
        ast::ConFields::Empty => {
            vec![l(
                loc,
                ast::Stmt::Expr(con_sel(loc, "Bool", Some("True")).node),
            )]
        }

        ast::ConFields::Named { fields, extension } => {
            let field_names: Vec<&ast::Name> = fields.iter().map(|(name, _)| name).collect();

            if extension.is_some() {
                let names: Vec<ast::Name> = fields.iter().map(|(name, _)| name.clone()).collect();
                let mut stmts = vec![
                    let_destructure_rest(loc, type_name, &names, "selfExts", var(loc, "self")),
                    let_destructure_rest(loc, type_name, &names, "otherExts", var(loc, "other")),
                ];
                let mut eq = chain_eq_fields(loc, &field_names, FieldAccess::SelfOther);
                let ext_eq = bin_op(
                    loc,
                    var(loc, "selfExts"),
                    ast::BinOp::Equal,
                    var(loc, "otherExts"),
                );
                eq = if field_names.is_empty() {
                    ext_eq
                } else {
                    bin_op(loc, eq, ast::BinOp::And, ext_eq)
                };
                stmts.push(l(loc, ast::Stmt::Expr(eq.node)));
                stmts
            } else {
                let expr = chain_eq_fields(loc, &field_names, FieldAccess::SelfOther);
                vec![l(loc, ast::Stmt::Expr(expr.node))]
            }
        }

        ast::ConFields::Unnamed { fields } => {
            let field_names: Vec<ast::Name> = (0..fields.len())
                .map(|i| ast::Name::new(format!("_{}", i)))
                .collect();
            let field_refs: Vec<&ast::Name> = field_names.iter().collect();
            let expr = chain_eq_fields(loc, &field_refs, FieldAccess::SelfOther);
            vec![l(loc, ast::Stmt::Expr(expr.node))]
        }
    }
}

/// Generate Eq body for a sum type.
///
/// ```ignore
/// match (l = self, r = other):
///     (l = Type.Con1, r = Type.Con1):
///         Bool.True
///     (l = Type.Con2(l0), r = Type.Con2(r0)):
///         l0 == r0
///     _:
///         Bool.False
/// ```
fn derive_eq_sum(
    loc: &ast::Loc,
    type_name: &ast::Name,
    cons: &[ast::ConDecl],
) -> Vec<ast::L<ast::Stmt>> {
    let scrutinee = record(loc, vec![("l", var(loc, "self")), ("r", var(loc, "other"))]);

    let mut alts: Vec<ast::Alt> = Vec::new();

    for con in cons {
        let (l_pats, r_pats, num_fields, has_extension) = match &con.fields {
            ast::ConFields::Empty => (vec![], vec![], 0, false),

            ast::ConFields::Named { fields, extension } => {
                let l_pats: Vec<ast::Named<ast::L<ast::Pat>>> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, (name, _))| ast::Named {
                        name: Some(name.clone()),
                        node: l(
                            loc,
                            ast::Pat::Var(ast::VarPat {
                                var: ast::Name::new(format!("l{}", i)),
                                ty: None,
                                refined: None,
                            }),
                        ),
                    })
                    .collect();

                let r_pats: Vec<ast::Named<ast::L<ast::Pat>>> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, (name, _))| ast::Named {
                        name: Some(name.clone()),
                        node: l(
                            loc,
                            ast::Pat::Var(ast::VarPat {
                                var: ast::Name::new(format!("r{}", i)),
                                ty: None,
                                refined: None,
                            }),
                        ),
                    })
                    .collect();

                (l_pats, r_pats, fields.len(), extension.is_some())
            }

            ast::ConFields::Unnamed { fields } => {
                let l_pats: Vec<ast::Named<ast::L<ast::Pat>>> = (0..fields.len())
                    .map(|i| ast::Named {
                        name: None,
                        node: l(
                            loc,
                            ast::Pat::Var(ast::VarPat {
                                var: ast::Name::new(format!("l{}", i)),
                                ty: None,
                                refined: None,
                            }),
                        ),
                    })
                    .collect();

                let r_pats: Vec<ast::Named<ast::L<ast::Pat>>> = (0..fields.len())
                    .map(|i| ast::Named {
                        name: None,
                        node: l(
                            loc,
                            ast::Pat::Var(ast::VarPat {
                                var: ast::Name::new(format!("r{}", i)),
                                ty: None,
                                refined: None,
                            }),
                        ),
                    })
                    .collect();

                (l_pats, r_pats, fields.len(), false)
            }
        };

        let l_rest = if has_extension {
            ast::RestPat::Bind(ast::VarPat {
                var: ast::Name::new_static("lExts"),
                ty: None,
                refined: None,
            })
        } else {
            ast::RestPat::No
        };

        let r_rest = if has_extension {
            ast::RestPat::Bind(ast::VarPat {
                var: ast::Name::new_static("rExts"),
                ty: None,
                refined: None,
            })
        } else {
            ast::RestPat::No
        };

        let l_con_pat = ast::Con {
            mod_prefix: None,
            ty: type_name.clone(),
            con: Some(con.name.clone()),
            ty_user_ty_args: vec![],
            con_user_ty_args: vec![],
            ty_args: vec![],
            resolved_ty_id: None,
            inferred_ty: None,
        };

        let r_con_pat = l_con_pat.clone();

        let l_pat = l(
            loc,
            ast::Pat::Con(ast::ConPat {
                con: l_con_pat,
                fields: l_pats,
                rest: l_rest,
            }),
        );

        let r_pat = l(
            loc,
            ast::Pat::Con(ast::ConPat {
                con: r_con_pat,
                fields: r_pats,
                rest: r_rest,
            }),
        );

        let record_pat = l(
            loc,
            ast::Pat::Record(ast::RecordPat {
                fields: vec![
                    ast::Named {
                        name: Some(ast::Name::new_static("l")),
                        node: l_pat,
                    },
                    ast::Named {
                        name: Some(ast::Name::new_static("r")),
                        node: r_pat,
                    },
                ],
                rest: ast::RestPat::No,
                inferred_ty: None,
            }),
        );

        let rhs = if num_fields == 0 && !has_extension {
            vec![l(
                loc,
                ast::Stmt::Expr(con_sel(loc, "Bool", Some("True")).node),
            )]
        } else {
            let mut eq_expr = if num_fields > 0 {
                let field_names: Vec<ast::Name> = (0..num_fields)
                    .map(|i| ast::Name::new(format!("{}", i)))
                    .collect();
                let field_refs: Vec<&ast::Name> = field_names.iter().collect();
                Some(chain_eq_fields(loc, &field_refs, FieldAccess::BoundVars))
            } else {
                None
            };

            if has_extension {
                let ext_eq = bin_op(loc, var(loc, "lExts"), ast::BinOp::Equal, var(loc, "rExts"));
                eq_expr = Some(match eq_expr {
                    Some(prev) => bin_op(loc, prev, ast::BinOp::And, ext_eq),
                    None => ext_eq,
                });
            }

            vec![l(loc, ast::Stmt::Expr(eq_expr.unwrap().node))]
        };

        alts.push(ast::Alt {
            pat: record_pat,
            guard: None,
            rhs,
        });
    }

    // Add wildcard catch-all: `_: Bool.False`
    alts.push(ast::Alt {
        pat: l(loc, ast::Pat::Ignore),
        guard: None,
        rhs: vec![l(
            loc,
            ast::Stmt::Expr(con_sel(loc, "Bool", Some("False")).node),
        )],
    });

    let match_expr = ast::Expr::Match(ast::MatchExpr {
        scrutinee: Box::new(scrutinee),
        alts,
        inferred_ty: None,
    });

    vec![l(loc, ast::Stmt::Expr(match_expr))]
}

enum FieldAccess {
    /// Access via `self.field` and `other.field`.
    SelfOther,

    /// Access via bound variables `l0`, `r0`, etc.
    BoundVars,
}

/// Chain `field1 == field2 && field3 == field4 && ...` for a list of field names.
fn chain_eq_fields(
    loc: &ast::Loc,
    field_names: &[&ast::Name],
    access: FieldAccess,
) -> ast::L<ast::Expr> {
    if field_names.is_empty() {
        return con_sel(loc, "Bool", Some("True"));
    }

    let mut result: Option<ast::L<ast::Expr>> = None;

    for (i, field_name) in field_names.iter().enumerate() {
        let (left, right) = match access {
            FieldAccess::SelfOther => (
                field_sel(loc, var(loc, "self"), field_name),
                field_sel(loc, var(loc, "other"), field_name),
            ),
            FieldAccess::BoundVars => (var(loc, &format!("l{}", i)), var(loc, &format!("r{}", i))),
        };

        let eq = bin_op(loc, left, ast::BinOp::Equal, right);

        result = Some(match result {
            None => eq,
            Some(acc) => bin_op(loc, acc, ast::BinOp::And, eq),
        });
    }

    result.unwrap()
}
