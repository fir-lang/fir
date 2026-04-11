pub mod eq;
pub mod to_doc;

use crate::ast;
use crate::module_loader::LoadedPgm;
use crate::utils::loc_display;

use smol_str::SmolStr;

/// Expand all `#[derive(...)]` attributes in the program, generating `ImplDecl` nodes.
pub(crate) fn expand_derives(pgm: &mut LoadedPgm) {
    for module in pgm.modules.values_mut() {
        expand_derives_module(module);
    }
}

fn expand_derives_module(module: &mut ast::Module) {
    let mut new_impls: Vec<ast::L<ast::TopDecl>> = vec![];

    for decl in module.decls.iter() {
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

    module.decls.extend(new_impls);
}

/// Extract trait names from a `#[derive(Trait1, Trait2)]` attribute.
fn extract_derive_traits(attr: &ast::Attribute) -> Vec<ast::Name> {
    if attr.lhs.is_some() {
        return vec![];
    }

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
            id: ast::Name::new(name),
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
            field: ast::Name::new(field),
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
            ty: ast::Name::new(ty),
            ty_user_ty_args: vec![],
            member: ast::Name::new(member),
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
            ty: ast::Name::new(ty),
            con: con.map(ast::Name::new),
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
                .map(|(name, expr)| (ast::Name::new(name), expr))
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
                    var: ast::Name::new(name),
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
    type_name: &ast::Name,
    field_names: &[ast::Name],
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
                        var: ast::Name::new(rest_var),
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
    name: &ast::Name,
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
/// Generates `Trait[fieldType]` for each field type with a type variable in the declaration. For
/// extension fields `..ext`, generates `Trait[RecRowList[ext]]`.
fn trait_context(loc: &ast::Loc, trait_name: &str, type_decl: &ast::TypeDecl) -> ast::Context {
    let mut preds: Vec<ast::L<ast::Pred>> = vec![];

    // Because kind inference looks at one definition at a time, we have to collect row-kinded type
    // parameters from the type definition, and add kind annotations in the `impl` context.
    // Otherwise row-kinded type parameters in the type definition will get inferred kind `*` here.
    // See issue #318 for improving this.
    let type_row_params = collect_extension_row_params(type_decl);

    // Add kind annotations for row-typed type parameters (explicit or from extensions).
    let row_rec_kind = |loc: &ast::Loc| {
        l(
            loc,
            ast::Type::Named(ast::NamedType {
                name: ast::Name::new_static("Row"),
                args: vec![l(
                    loc,
                    ast::Type::Named(ast::NamedType {
                        name: ast::Name::new_static("Rec"),
                        args: vec![],
                    }),
                )],
            }),
        )
    };

    for p in &type_decl.type_params {
        if p.kind.is_some() || type_row_params.contains(&p.name.node) {
            preds.push(l(
                loc,
                ast::Pred::Kind {
                    var: p.name.node.clone(),
                    kind: Some(p.kind.clone().unwrap_or_else(|| row_rec_kind(loc))),
                },
            ));
        }
    }

    // Collect all field types and generate `Trait[fieldType]` (or `Trait[RecRowList[fieldType]]`
    // for extensions), if the field type  for each polymorphic field type.
    for field_ty in collect_polymorphic_field_types(loc, type_decl) {
        preds.push(l(
            loc,
            ast::Pred::App(ast::NamedType {
                name: ast::Name::new(trait_name),
                args: vec![field_ty],
            }),
        ));
    }

    ast::Context {
        type_params: vec![],
        preds,
    }
}

/// Collect type param names used directly as row extensions (e.g. `..t`).
///
/// This is a hack and we should consider removing this. See the use site for why this function is
/// needed.
fn collect_extension_row_params(type_decl: &ast::TypeDecl) -> Vec<ast::Name> {
    let mut row_params: Vec<ast::Name> = vec![];

    let mut collect_from_fields = |fields: &ast::ConFields| {
        if let ast::ConFields::Named {
            fields: _,
            extension: Some(ext),
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

/// Collect field types with type variables.
///
/// These will be used in `impl` context predicates, so for extension fields (`..ext`) this collects
/// `RecRowList[ext]`.
fn collect_polymorphic_field_types(
    loc: &ast::Loc,
    type_decl: &ast::TypeDecl,
) -> Vec<ast::L<ast::Type>> {
    let mut types: Vec<ast::L<ast::Type>> = vec![];

    let mut collect_from_fields = |fields: &ast::ConFields| match fields {
        ast::ConFields::Empty => {}

        ast::ConFields::Named { fields, extension } => {
            for (_name, ty) in fields {
                if ty_has_vars(&ty.node) {
                    types.push(ty.clone());
                }
            }
            if let Some(ext) = extension
                && ty_has_vars(&ext.node)
            {
                types.push(l(
                    loc,
                    ast::Type::Named(ast::NamedType {
                        name: ast::Name::new_static("RecRowList"),
                        args: vec![l(&ext.loc, ext.node.clone())],
                    }),
                ));
            }
        }

        ast::ConFields::Unnamed { fields } => {
            for ty in fields {
                if ty_has_vars(&ty.node) {
                    types.push(ty.clone());
                }
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

/// Whether the type has a type variable.
///
/// These types are polymorphic in the type declaration, so they'll need prediactes in `impl`
/// contexts.
fn ty_has_vars(ty: &ast::Type) -> bool {
    match ty {
        ast::Type::Var(_) => true,

        ast::Type::Named(named) => named.args.iter().any(|a| ty_has_vars(&a.node)),

        ast::Type::Record {
            fields,
            extension,
            is_row: _,
        } => {
            fields.iter().any(|(_, t)| ty_has_vars(t))
                || extension.as_ref().is_some_and(|e| ty_has_vars(&e.node))
        }

        ast::Type::Fn(fn_ty) => {
            fn_ty.args.iter().any(|a| ty_has_vars(&a.node))
                || fn_ty.ret.as_ref().is_some_and(|r| ty_has_vars(&r.node))
        }

        ast::Type::Variant {
            alts,
            extension,
            is_row: _,
        } => {
            alts.iter()
                .any(|a| a.args.iter().any(|arg| ty_has_vars(&arg.node)))
                || extension.as_ref().is_some_and(|e| ty_has_vars(&e.node))
        }

        ast::Type::AssocTySelect { ty, assoc_ty: _ } => ty_has_vars(&ty.node),
    }
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
                trait_: l(loc, ast::Name::new(trait_name)),
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
    params: Vec<(ast::Name, ast::L<ast::Type>)>,
    return_ty: ast::L<ast::Type>,
    body: Vec<ast::L<ast::Stmt>>,
) -> ast::FunDecl {
    ast::FunDecl {
        parent_ty: None,
        name: l(loc, ast::Name::new(name)),
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
