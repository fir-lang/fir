pub mod eq;
pub mod to_doc;

use crate::ast;
use crate::utils::loc_display;

use smol_str::SmolStr;

/// Expand all `#[derive(...)]` attributes in the module, generating `ImplDecl` nodes.
pub(crate) fn expand_derives(module: &mut ast::Module) {
    let mut new_impls: Vec<ast::L<ast::TopDecl>> = vec![];

    for decl in module.iter() {
        if let ast::TopDecl::Type(type_decl) = &decl.node {
            let Some(attr) = &type_decl.node.attr else {
                continue;
            };

            let attr_loc = attr.expr.loc.clone();
            let traits = extract_derive_traits(attr);

            if traits.is_empty() {
                continue;
            }

            if let Some(ast::TypeDeclRhs::Synonym(_)) = &type_decl.node.rhs {
                panic!(
                    "{}: Cannot derive traits for type synonym `{}`",
                    loc_display(&attr_loc),
                    type_decl.node.name,
                );
            }

            for trait_name in &traits {
                match trait_name.as_str() {
                    "Eq" => {
                        new_impls.push(eq::derive_eq(&type_decl.node, &attr_loc));
                    }
                    "ToDoc" => {
                        new_impls.push(to_doc::derive_to_doc(&type_decl.node, &attr_loc));
                    }
                    other => {
                        panic!("{}: Unknown derive trait `{other}`", loc_display(&attr_loc));
                    }
                }
            }
        }
    }

    module.extend(new_impls);
}

/// Extract trait names from a `#[derive(Trait1, Trait2)]` attribute.
fn extract_derive_traits(attr: &ast::Attribute) -> Vec<ast::Id> {
    let ast::Expr::Call(call) = &attr.expr.node else {
        return vec![];
    };

    let ast::Expr::Var(var) = &call.fun.node else {
        return vec![];
    };

    if var.id != "derive" {
        return vec![];
    }

    let mut traits = Vec::with_capacity(call.args.len());
    for arg in &call.args {
        if let ast::Expr::ConSel(con) = &arg.expr.node
            && con.con.is_none()
        {
            traits.push(con.ty.clone());
        }
    }
    traits
}

////////////////////////////////////////////////////////////////////////////////////////////////////
// Helpers below to help creating AST nodes

/// Create a located node using the given attribute location.
fn l<T>(loc: &ast::Loc, node: T) -> ast::L<T> {
    ast::L {
        loc: loc.clone(),
        node,
    }
}

fn var(loc: &ast::Loc, name: &str) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::Var(ast::VarExpr {
            id: SmolStr::new(name),
            user_ty_args: vec![],
            ty_args: vec![],
            inferred_ty: None,
        }),
    )
}

fn field_sel(loc: &ast::Loc, obj: ast::L<ast::Expr>, field: &str) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::FieldSel(ast::FieldSelExpr {
            object: Box::new(obj),
            field: SmolStr::new(field),
            user_ty_args: vec![],
            inferred_ty: None,
        }),
    )
}

fn method_call(
    loc: &ast::Loc,
    obj: ast::L<ast::Expr>,
    method: &str,
    args: Vec<ast::L<ast::Expr>>,
) -> ast::L<ast::Expr> {
    let sel = field_sel(loc, obj, method);
    call(loc, sel, args)
}

fn call(loc: &ast::Loc, fun: ast::L<ast::Expr>, args: Vec<ast::L<ast::Expr>>) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::Call(ast::CallExpr {
            fun: Box::new(fun),
            args: args
                .into_iter()
                .map(|expr| ast::CallArg { name: None, expr })
                .collect(),
            splice: None,
            inferred_ty: None,
        }),
    )
}

fn assoc_fn_sel(loc: &ast::Loc, ty: &str, member: &str) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::AssocFnSel(ast::AssocFnSelExpr {
            ty: SmolStr::new(ty),
            ty_user_ty_args: vec![],
            member: SmolStr::new(member),
            user_ty_args: vec![],
            ty_args: vec![],
            inferred_ty: None,
        }),
    )
}

fn assoc_fn_call(
    loc: &ast::Loc,
    ty: &str,
    func: &str,
    args: Vec<ast::L<ast::Expr>>,
) -> ast::L<ast::Expr> {
    call(loc, assoc_fn_sel(loc, ty, func), args)
}

fn con_sel(loc: &ast::Loc, ty: &str, con: Option<&str>) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::ConSel(ast::Con {
            ty: SmolStr::new(ty),
            con: con.map(SmolStr::new),
            user_ty_args: vec![],
            ty_args: vec![],
            inferred_ty: None,
        }),
    )
}

fn bin_op(
    loc: &ast::Loc,
    left: ast::L<ast::Expr>,
    op: ast::BinOp,
    right: ast::L<ast::Expr>,
) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::BinOp(ast::BinOpExpr {
            left: Box::new(left),
            right: Box::new(right),
            op,
        }),
    )
}

// expr + expr (Doc concatenation via Add)
fn add(loc: &ast::Loc, left: ast::L<ast::Expr>, right: ast::L<ast::Expr>) -> ast::L<ast::Expr> {
    bin_op(loc, left, ast::BinOp::Add, right)
}

fn str_lit(loc: &ast::Loc, s: &str) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::Str(vec![crate::interpolation::StrPart::Str(s.to_owned())]),
    )
}

fn u32_lit(loc: &ast::Loc, n: u32) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::Int(ast::IntExpr {
            text: SmolStr::new(n.to_string()),
            kind: None,
            parsed: n as u64,
        }),
    )
}

fn char_lit(loc: &ast::Loc, c: char) -> ast::L<ast::Expr> {
    l(loc, ast::Expr::Char(c))
}

fn record(loc: &ast::Loc, fields: Vec<(&str, ast::L<ast::Expr>)>) -> ast::L<ast::Expr> {
    l(
        loc,
        ast::Expr::Record(ast::RecordExpr {
            fields: fields
                .into_iter()
                .map(|(name, expr)| (SmolStr::new(name), expr))
                .collect(),
            splice: None,
            inferred_ty: None,
        }),
    )
}

// let args = <expr>
fn let_stmt(loc: &ast::Loc, name: &str, rhs: ast::L<ast::Expr>) -> ast::L<ast::Stmt> {
    l(
        loc,
        ast::Stmt::Let(ast::LetStmt {
            lhs: l(
                loc,
                ast::Pat::Var(ast::VarPat {
                    var: SmolStr::new(name),
                    ty: None,
                    refined: None,
                }),
            ),
            ty: None,
            rhs,
        }),
    )
}

/// `let TypeName(field1 = _, field2 = _, ..rest_var) = rhs`
///
/// Creates a let statement that destructures a product type, ignoring named fields and binding the
/// rest to `rest_var`.
fn let_destructure_rest(
    loc: &ast::Loc,
    type_name: &ast::Id,
    field_names: &[ast::Id],
    rest_var: &str,
    rhs: ast::L<ast::Expr>,
) -> ast::L<ast::Stmt> {
    let fields: Vec<ast::Named<ast::L<ast::Pat>>> = field_names
        .iter()
        .map(|name| ast::Named {
            name: Some(name.clone()),
            node: l(loc, ast::Pat::Ignore),
        })
        .collect();

    l(
        loc,
        ast::Stmt::Let(ast::LetStmt {
            lhs: l(
                loc,
                ast::Pat::Con(ast::ConPat {
                    con: ast::Con {
                        ty: type_name.clone(),
                        con: None,
                        user_ty_args: vec![],
                        ty_args: vec![],
                        inferred_ty: None,
                    },
                    fields,
                    rest: ast::RestPat::Bind(ast::VarPat {
                        var: SmolStr::new(rest_var),
                        ty: None,
                        refined: None,
                    }),
                }),
            ),
            ty: None,
            rhs,
        }),
    )
}

// args += <expr>
fn plus_eq_stmt(loc: &ast::Loc, name: &str, rhs: ast::L<ast::Expr>) -> ast::L<ast::Stmt> {
    l(
        loc,
        ast::Stmt::Assign(ast::AssignStmt {
            lhs: var(loc, name),
            rhs,
            op: ast::AssignOp::PlusEq,
        }),
    )
}

// args = <expr>
fn assign_stmt(loc: &ast::Loc, name: &str, rhs: ast::L<ast::Expr>) -> ast::L<ast::Stmt> {
    l(
        loc,
        ast::Stmt::Assign(ast::AssignStmt {
            lhs: var(loc, name),
            rhs,
            op: ast::AssignOp::Eq,
        }),
    )
}

fn type_with_params(
    loc: &ast::Loc,
    name: &ast::Id,
    type_params: &[ast::TypeParam],
) -> ast::L<ast::Type> {
    l(
        loc,
        ast::Type::Named(ast::NamedType {
            name: name.clone(),
            args: type_params
                .iter()
                .map(|p| l(loc, ast::Type::Var(p.name.node.clone())))
                .collect(),
        }),
    )
}

/// Build the impl context for a derived trait.
///
/// Generates `Trait[field_type]` for each field type in the declaration. For extension fields
/// (`..ext`), generates `Trait[(..ext)]`.
///
/// Also adds kind annotations for row-typed type parameters (from extensions or explicit kind
/// annotations).
fn trait_context(loc: &ast::Loc, trait_name: &str, type_decl: &ast::TypeDecl) -> ast::Context {
    let mut preds: Vec<ast::L<ast::Pred>> = vec![];

    // Collect type param names used as extensions (e.g. `..t`), these are row-kinded.
    let ext_row_params = collect_extension_row_params(type_decl);

    // Add kind annotations for row-typed type parameters (explicit or from extensions).
    let row_rec_kind = |loc: &ast::Loc| {
        l(
            loc,
            ast::Type::Named(ast::NamedType {
                name: SmolStr::new_static("Row"),
                args: vec![l(
                    loc,
                    ast::Type::Named(ast::NamedType {
                        name: SmolStr::new_static("Rec"),
                        args: vec![],
                    }),
                )],
            }),
        )
    };
    for p in &type_decl.type_params {
        if p.kind.is_some() || ext_row_params.contains(&p.name.node) {
            preds.push(l(
                loc,
                ast::Pred::Kind {
                    var: p.name.node.clone(),
                    kind: Some(p.kind.clone().unwrap_or_else(|| row_rec_kind(loc))),
                },
            ));
        }
    }

    // Collect all field types and generate Trait[field_type] for each polymorphic, non-recursive
    // field type. Concrete types (no type variables) don't need predicates, the solver resolves
    // those directly. Recursive types (referencing the type being derived) are skipped to avoid
    // infinite predicate cycles.
    let type_param_names: Vec<&ast::Id> =
        type_decl.type_params.iter().map(|p| &p.name.node).collect();
    let field_types = collect_field_types(loc, type_decl);
    for field_ty in &field_types {
        if ty_has_vars(&field_ty.node, &type_param_names)
            && !ty_mentions(&field_ty.node, &type_decl.name)
        {
            preds.push(l(
                loc,
                ast::Pred::App(ast::NamedType {
                    name: SmolStr::new(trait_name),
                    args: vec![field_ty.clone()],
                }),
            ));
        }
    }

    // For recursive field types (those mentioning the type being derived), fall back to
    // generating Trait[param] for each type parameter they use.
    for field_ty in &field_types {
        if ty_has_vars(&field_ty.node, &type_param_names)
            && ty_mentions(&field_ty.node, &type_decl.name)
        {
            for p in &type_decl.type_params {
                if ty_has_vars(&field_ty.node, &[&p.name.node]) {
                    let arg = if p.kind.is_some() || ext_row_params.contains(&p.name.node) {
                        l(
                            loc,
                            ast::Type::Named(ast::NamedType {
                                name: SmolStr::new_static("RecRowList"),
                                args: vec![l(loc, ast::Type::Var(p.name.node.clone()))],
                            }),
                        )
                    } else {
                        l(loc, ast::Type::Var(p.name.node.clone()))
                    };
                    preds.push(l(
                        loc,
                        ast::Pred::App(ast::NamedType {
                            name: SmolStr::new(trait_name),
                            args: vec![arg],
                        }),
                    ));
                }
            }
        }
    }

    ast::Context {
        type_params: vec![],
        preds,
    }
}

/// Check if a type references any of the given type parameter names.
fn ty_has_vars(ty: &ast::Type, params: &[&ast::Id]) -> bool {
    match ty {
        ast::Type::Var(v) => params.contains(&v),
        ast::Type::Named(named) => named.args.iter().any(|a| ty_has_vars(&a.node, params)),
        ast::Type::Record {
            fields, extension, ..
        } => {
            fields.iter().any(|(_, t)| ty_has_vars(t, params))
                || extension
                    .as_ref()
                    .is_some_and(|e| ty_has_vars(&e.node, params))
        }
        ast::Type::Fn(fn_ty) => {
            fn_ty.args.iter().any(|a| ty_has_vars(&a.node, params))
                || fn_ty
                    .ret
                    .as_ref()
                    .is_some_and(|r| ty_has_vars(&r.node, params))
        }
        ast::Type::Variant {
            alts, extension, ..
        } => {
            alts.iter()
                .any(|a| a.args.iter().any(|arg| ty_has_vars(&arg.node, params)))
                || extension
                    .as_ref()
                    .is_some_and(|e| ty_has_vars(&e.node, params))
        }
        ast::Type::AssocTySelect { ty, .. } => ty_has_vars(&ty.node, params),
    }
}

/// Check if a type mentions a specific named type constructor.
fn ty_mentions(ty: &ast::Type, name: &ast::Id) -> bool {
    match ty {
        ast::Type::Var(_) => false,
        ast::Type::Named(named) => {
            named.name == *name || named.args.iter().any(|a| ty_mentions(&a.node, name))
        }
        ast::Type::Record {
            fields, extension, ..
        } => {
            fields.iter().any(|(_, t)| ty_mentions(t, name))
                || extension
                    .as_ref()
                    .is_some_and(|e| ty_mentions(&e.node, name))
        }
        ast::Type::Fn(fn_ty) => {
            fn_ty.args.iter().any(|a| ty_mentions(&a.node, name))
                || fn_ty
                    .ret
                    .as_ref()
                    .is_some_and(|r| ty_mentions(&r.node, name))
        }
        ast::Type::Variant {
            alts, extension, ..
        } => {
            alts.iter()
                .any(|a| a.args.iter().any(|arg| ty_mentions(&arg.node, name)))
                || extension
                    .as_ref()
                    .is_some_and(|e| ty_mentions(&e.node, name))
        }
        ast::Type::AssocTySelect { ty, .. } => ty_mentions(&ty.node, name),
    }
}

/// Collect type param names used directly as row extensions (e.g. `..t`).
fn collect_extension_row_params(type_decl: &ast::TypeDecl) -> Vec<ast::Id> {
    let mut row_params: Vec<ast::Id> = vec![];

    let mut collect_from_fields = |fields: &ast::ConFields| {
        if let ast::ConFields::Named {
            extension: Some(ext),
            ..
        } = fields
            && let ast::Type::Var(var) = &ext.node
            && !row_params.contains(var)
        {
            row_params.push(var.clone());
        }
    };

    match &type_decl.rhs {
        Some(ast::TypeDeclRhs::Product(fields)) => collect_from_fields(fields),
        Some(ast::TypeDeclRhs::Sum { cons, .. }) => {
            for con in cons {
                collect_from_fields(&con.fields);
            }
        }
        _ => {}
    }

    row_params
}

/// Collect all field types from a type declaration.
///
/// For named fields, collects each field's type. For unnamed fields, collects each positional
/// type. For extension fields (`..ext`), collects `RecRowList[ext]` (not `(..ext)`, which would
/// cause the trait solver to loop).
fn collect_field_types(loc: &ast::Loc, type_decl: &ast::TypeDecl) -> Vec<ast::L<ast::Type>> {
    let mut types: Vec<ast::L<ast::Type>> = vec![];

    let mut collect_from_fields = |fields: &ast::ConFields| match fields {
        ast::ConFields::Empty => {}
        ast::ConFields::Named { fields, extension } => {
            for (_name, ty) in fields {
                types.push(ty.clone());
            }
            if let Some(ext) = extension {
                types.push(l(
                    loc,
                    ast::Type::Named(ast::NamedType {
                        name: SmolStr::new_static("RecRowList"),
                        args: vec![l(&ext.loc, ext.node.clone())],
                    }),
                ));
            }
        }
        ast::ConFields::Unnamed { fields } => {
            for ty in fields {
                types.push(ty.clone());
            }
        }
    };

    match &type_decl.rhs {
        Some(ast::TypeDeclRhs::Product(fields)) => collect_from_fields(fields),
        Some(ast::TypeDeclRhs::Sum { cons, .. }) => {
            for con in cons {
                collect_from_fields(&con.fields);
            }
        }
        _ => {}
    }

    types
}

/// Build an `ImplDecl` wrapping a single `FunDecl`, as a `TopDecl`.
fn make_impl_top_decl(
    loc: &ast::Loc,
    trait_name: &str,
    type_decl: &ast::TypeDecl,
    fun: ast::FunDecl,
) -> ast::L<ast::TopDecl> {
    let ty = type_with_params(loc, &type_decl.name, &type_decl.type_params);
    l(
        loc,
        ast::TopDecl::Impl(l(
            loc,
            ast::ImplDecl {
                context: trait_context(loc, trait_name, type_decl),
                trait_: l(loc, SmolStr::new(trait_name)),
                tys: vec![ty],
                items: vec![ast::ImplDeclItem::Fun(l(loc, fun))],
            },
        )),
    )
}

fn make_method(
    loc: &ast::Loc,
    name: &str,
    self_ty: ast::L<ast::Type>,
    params: Vec<(ast::Id, ast::L<ast::Type>)>,
    return_ty: ast::L<ast::Type>,
    body: Vec<ast::L<ast::Stmt>>,
) -> ast::FunDecl {
    ast::FunDecl {
        parent_ty: None,
        name: l(loc, SmolStr::new(name)),
        sig: ast::FunSig {
            context: ast::Context::default(),
            self_: ast::SelfParam::Explicit(self_ty),
            params: params
                .into_iter()
                .map(|(name, ty)| (name, Some(ty)))
                .collect(),
            return_ty: Some(return_ty),
            exceptions: None,
        },
        body: Some(body),
    }
}
