use crate::ast;
use crate::collections::Set;

use smol_str::SmolStr;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RecordShape {
    UnnamedFields {
        arity: u32,
    },

    NamedFields {
        // Sorted.
        fields: Vec<SmolStr>,
    },
}

impl RecordShape {
    pub fn from_named_things<T>(things: &[ast::Named<T>]) -> RecordShape {
        // All or none of the fields should be named.
        if things.is_empty() {
            return RecordShape::UnnamedFields { arity: 0 };
        }

        if things[0].name.is_some() {
            let mut names: Set<SmolStr> = Default::default();
            for thing in things {
                let new = names.insert(thing.name.clone().unwrap());
                assert!(new);
            }
            let mut fields: Vec<SmolStr> = names.into_iter().collect();
            fields.sort();
            RecordShape::NamedFields { fields }
        } else {
            RecordShape::UnnamedFields {
                arity: things.len() as u32,
            }
        }
    }
}

pub fn collect_records(pgm: &[ast::L<ast::TopDecl>]) -> Set<RecordShape> {
    let mut records: Set<RecordShape> = Default::default();

    for decl in pgm {
        match &decl.thing {
            ast::TopDecl::Type(ty_decl) => visit_ty_decl(&ty_decl.thing, &mut records),
            ast::TopDecl::Fun(fun_decl) => visit_fun_decl(&fun_decl.thing, &mut records),
        }
    }

    records
}

fn visit_ty_decl(ty_decl: &ast::TypeDecl, records: &mut Set<RecordShape>) {
    match &ty_decl.rhs {
        ast::TypeDeclRhs::Sum(constrs) => {
            for constr in constrs {
                visit_fields(&constr.fields, records);
            }
        }
        ast::TypeDeclRhs::Product(fields) => {
            visit_fields(fields, records);
        }
    }
}

fn visit_fun_decl(fun_decl: &ast::FunDecl, records: &mut Set<RecordShape>) {
    for (_param_name, param_ty) in &fun_decl.params {
        visit_ty(param_ty, records);
    }

    if let Some(return_ty) = &fun_decl.return_ty {
        visit_ty(return_ty, records);
    }

    for stmt in &fun_decl.body.thing {
        visit_stmt(&stmt.thing, records);
    }
}

fn visit_fields(fields: &ast::ConstructorFields, records: &mut Set<RecordShape>) {
    match fields {
        ast::ConstructorFields::Empty => {}

        ast::ConstructorFields::Named(named_fields) => named_fields
            .iter()
            .for_each(|(_name, ty)| visit_ty(ty, records)),

        ast::ConstructorFields::Unnamed(fields) => {
            fields.iter().for_each(|ty| visit_ty(ty, records))
        }
    }
}

fn visit_ty(ty: &ast::Type, records: &mut Set<RecordShape>) {
    match ty {
        ast::Type::Named(ast::NamedType { name: _, args }) => {
            args.iter().for_each(|ty| visit_ty(ty, records))
        }

        ast::Type::Record(fields) => {
            records.insert(RecordShape::from_named_things(fields));
        }
    }
}

fn visit_stmt(stmt: &ast::Stmt, records: &mut Set<RecordShape>) {
    match stmt {
        ast::Stmt::Let(ast::LetStatement { lhs: _, ty, rhs }) => {
            // visit_pat(lhs, records);
            if let Some(ty) = ty {
                visit_ty(ty, records);
            }
            visit_expr(&rhs.thing, records);
        }

        // ast::Statement::LetFn(ast::FunDecl {
        //     type_name: _,
        //     name: _,
        //     type_params: _,
        //     predicates: _,
        //     self_: _,
        //     params,
        //     return_ty,
        //     body,
        // }) => {
        //     for (_param_name, param_ty) in params {
        //         visit_ty(param_ty, records);
        //     }
        //     if let Some(return_ty) = return_ty {
        //         visit_ty(return_ty, records);
        //     }

        //     for stmt in body {
        //         visit_stmt(stmt, records);
        //     }
        // }
        ast::Stmt::Match(ast::MatchStatement { scrutinee, alts }) => {
            visit_expr(&scrutinee.thing, records);
            for alt in alts {
                visit_pat(&alt.pattern.thing, records);
                if let Some(guard) = &alt.guard {
                    visit_expr(&guard.thing, records);
                }
                for stmt in &alt.rhs {
                    visit_stmt(&stmt.thing, records);
                }
            }
        }

        ast::Stmt::If(ast::IfStatement {
            branches,
            else_branch,
        }) => {
            for (expr, stmts) in branches {
                visit_expr(&expr.thing, records);
                for stmt in stmts {
                    visit_stmt(&stmt.thing, records);
                }
            }
            if let Some(else_branch) = else_branch {
                for stmt in else_branch {
                    visit_stmt(&stmt.thing, records);
                }
            }
        }

        ast::Stmt::Assign(ast::AssignStatement { lhs, rhs, op: _ }) => {
            visit_expr(&lhs.thing, records);
            visit_expr(&rhs.thing, records);
        }

        ast::Stmt::Expr(expr) => visit_expr(&expr.thing, records),

        // ast::Statement::For(ast::ForStatement {
        //     var: _,
        //     ty,
        //     expr,
        //     body,
        // }) => {
        //     if let Some(ty) = ty {
        //         visit_ty(ty, records);
        //     }
        //     visit_expr(expr, records);
        //     for stmt in body {
        //         visit_stmt(stmt, records);
        //     }
        // }
        ast::Stmt::While(ast::WhileStatement { cond, body }) => {
            visit_expr(&cond.thing, records);
            for stmt in body {
                visit_stmt(&stmt.thing, records);
            }
        }

        ast::Stmt::Return(expr) => visit_expr(&expr.thing, records),
    }
}

fn visit_pat(pat: &ast::Pat, records: &mut Set<RecordShape>) {
    match pat {
        ast::Pat::Var(_) | ast::Pat::Ignore => {}

        ast::Pat::Constr(ast::ConstrPattern { constr: _, fields }) => {
            for field in fields {
                visit_pat(&field.thing.thing, records);
            }
        }

        ast::Pat::Record(fields) => {
            for field in fields {
                visit_pat(&field.thing.thing, records);
            }
            records.insert(RecordShape::from_named_things(fields));
        }
    }
}

fn visit_expr(expr: &ast::Expr, records: &mut Set<RecordShape>) {
    match expr {
        ast::Expr::Var(_)
        | ast::Expr::UpperVar(_)
        | ast::Expr::Int(_)
        | ast::Expr::String(_)
        | ast::Expr::Self_ => {}

        ast::Expr::FieldSelect(ast::FieldSelectExpr { object, field: _ }) => {
            visit_expr(&object.thing, records);
        }

        ast::Expr::ConstrSelect(_) => {}

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            visit_expr(&fun.thing, records);
            for arg in args {
                visit_expr(&arg.expr.thing, records);
            }
        }

        // ast::Expr::Range(ast::RangeExpr {
        //     from,
        //     to,
        //     inclusive: _,
        // }) => {
        //     visit_expr(from, records);
        //     visit_expr(to, records);
        // }
        ast::Expr::BinOp(ast::BinOpExpr { left, right, op: _ }) => {
            visit_expr(&left.thing, records);
            visit_expr(&right.thing, records);
        }

        ast::Expr::UnOp(ast::UnOpExpr { op: _, expr }) => {
            visit_expr(&expr.thing, records);
        }

        ast::Expr::ArrayIndex(ast::ArrayIndexExpr { array, index }) => {
            visit_expr(&array.thing, records);
            visit_expr(&index.thing, records);
        }

        ast::Expr::Record(fields) => {
            for field in fields {
                visit_expr(&field.thing.thing, records);
            }
            records.insert(RecordShape::from_named_things(fields));
        }
    }
}
