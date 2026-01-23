use crate::lowering::*;
use crate::mono_ast as mono;
use crate::utils::loc_display;

use std::fmt::Write;

pub fn print_pgm(pgm: &LoweredPgm) {
    let mut s = String::new();
    pgm.print(&mut s);
    println!("{s}");
}

impl LoweredPgm {
    pub fn print(&self, buf: &mut String) {
        for (heap_obj_idx, heap_obj) in self.heap_objs.iter().enumerate() {
            write!(buf, "heap_obj{heap_obj_idx}: ").unwrap();
            match heap_obj {
                HeapObj::Builtin(builtin) => write!(buf, "{builtin:?}").unwrap(),

                HeapObj::Source(SourceConDecl {
                    name,
                    idx,
                    ty_args,
                    fields,
                }) => {
                    assert_eq!(idx.0 as usize, heap_obj_idx);
                    buf.push_str(name.as_str());
                    print_ty_args(ty_args, buf);
                    buf.push('(');
                    for (i, field_ty) in fields.iter().enumerate() {
                        if i != 0 {
                            buf.push_str(", ");
                        }
                        field_ty.print(buf);
                    }
                    buf.push(')');
                }

                HeapObj::Record(record) => write!(buf, "{record:?}").unwrap(),
            }
            buf.push('\n');
        }

        buf.push('\n');

        for (fun_idx, fun) in self.funs.iter().enumerate() {
            match &fun.body {
                FunBody::Builtin(builtin) => writeln!(buf, "// {:?}", builtin).unwrap(),
                FunBody::Source(_) => {
                    writeln!(buf, "// {}", loc_display(&fun.name.loc)).unwrap();
                }
            }
            write!(buf, "fun{fun_idx}: ").unwrap();
            match &fun.body {
                FunBody::Builtin(builtin) => write!(buf, "{builtin:?}").unwrap(),

                FunBody::Source(SourceFunDecl { locals, body }) => {
                    assert_eq!(fun.idx.0 as usize, fun_idx);
                    if let Some(parent_ty) = &fun.parent_ty {
                        write!(buf, "{}.", parent_ty.node).unwrap();
                    }
                    buf.push_str(fun.name.node.as_str());
                    print_ty_args(&fun.ty_args, buf);
                    buf.push('\n');

                    buf.push_str("  locals: ");
                    for (i, local) in locals.iter().enumerate() {
                        if i != 0 {
                            buf.push_str(", ");
                        }
                        write!(buf, "{}: {}: ", i, local.name).unwrap();
                        local.ty.print(buf);
                    }
                    buf.push('\n');

                    buf.push_str("  params: ");
                    for (i, arg) in fun.params.iter().enumerate() {
                        if i != 0 {
                            buf.push_str(", ");
                        }
                        arg.print(buf);
                    }
                    buf.push('\n');

                    buf.push_str("  return_ty: ");
                    fun.return_ty.print(buf);
                    buf.push('\n');

                    buf.push_str("  exceptions: ");
                    fun.exceptions.print(buf);
                    buf.push('\n');
                    buf.push('\n');

                    for stmt in body {
                        buf.push_str(&INDENTS[0..2]);
                        stmt.node.print(buf, 2);
                    }
                }
            }
            buf.push('\n');
        }

        for (
            closure_idx,
            Closure {
                idx,
                locals,
                fvs,
                params,
                return_ty,
                exceptions,
                body,
                loc,
            },
        ) in self.closures.iter().enumerate()
        {
            assert_eq!(idx.0 as usize, closure_idx);
            writeln!(buf, "// {}", loc_display(loc)).unwrap();
            writeln!(buf, "closure{closure_idx}:").unwrap();

            buf.push_str("  locals: ");
            for (i, LocalInfo { name, ty }) in locals.iter().enumerate() {
                if i != 0 {
                    buf.push_str(", ");
                }
                buf.push_str(name.as_str());
                buf.push_str(": ");
                ty.print(buf);
            }
            buf.push('\n');

            buf.push_str("  fvs: ");
            for (
                i,
                ClosureFv {
                    id,
                    alloc_idx,
                    use_idx,
                },
            ) in fvs.iter().enumerate()
            {
                if i != 0 {
                    buf.push_str(", ");
                }
                write!(buf, "{}(alloc={}, use={})", id, alloc_idx.0, use_idx.0).unwrap();
            }
            buf.push('\n');

            buf.push_str("  params: ");
            for (i, arg) in params.iter().enumerate() {
                if i != 0 {
                    buf.push_str(", ");
                }
                arg.print(buf);
            }
            buf.push('\n');

            buf.push_str("  return_ty: ");
            return_ty.print(buf);
            buf.push('\n');

            buf.push_str("  exceptions: ");
            exceptions.print(buf);
            buf.push('\n');
            buf.push('\n');

            for stmt in body {
                buf.push_str(&INDENTS[0..2]);
                stmt.node.print(buf, 2);
            }

            buf.push('\n');
        }
    }
}

impl Stmt {
    pub fn print(&self, buf: &mut String, indent: u32) {
        match self {
            Stmt::Let(LetStmt {
                lhs,
                rhs,
                rhs_ty: _,
            }) => {
                buf.push_str("let ");
                lhs.node.print(buf);
                buf.push_str(" = ");
                rhs.node.print(buf, indent);
            }

            Stmt::Assign(AssignStmt { lhs, rhs }) => {
                lhs.node.print(buf, indent);
                buf.push_str(" = ");
                rhs.node.print(buf, indent);
            }

            Stmt::Expr(expr) => expr.print(buf, indent),

            Stmt::While(WhileStmt { label, cond, body }) => {
                if let Some(label) = label {
                    write!(buf, "{label}: ").unwrap();
                }
                buf.push_str("while ");
                cond.node.print(buf, indent);
                buf.push_str(":\n");
                for stmt in body {
                    buf.push_str(&INDENTS[0..(indent + 2) as usize]);
                    stmt.node.print(buf, indent + 2);
                }
            }

            Stmt::Break { label, level: _ } => match label {
                Some(label) => write!(buf, "break {label}").unwrap(),
                None => buf.push_str("break"),
            },

            Stmt::Continue { label, level: _ } => match label {
                Some(label) => write!(buf, "continue {label}").unwrap(),
                None => buf.push_str("continue"),
            },
        }

        buf.push('\n');
    }
}

impl Expr {
    pub fn print(&self, buf: &mut String, indent: u32) {
        match self {
            Expr::LocalVar(idx) => write!(buf, "local{}", idx.0).unwrap(),

            Expr::Fun(idx) => write!(buf, "fun{}", idx.0).unwrap(),

            Expr::Con(idx) => write!(buf, "con{}", idx.0).unwrap(),

            Expr::ConAlloc(idx, args, _con_ty) => {
                write!(buf, "con{}", idx.0).unwrap();
                buf.push('(');
                for (i, expr) in args.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    expr.node.print(buf, indent);
                }
                buf.push(')');
            }

            Expr::FieldSel(FieldSelExpr {
                object,
                field,
                idx: _,
                object_ty: _,
            }) => {
                object.node.print(buf, indent);
                buf.push('.');
                buf.push_str(field);
            }

            Expr::Call(CallExpr { fun, args }) => {
                fun.node.print(buf, indent);
                buf.push('(');
                for (i, expr) in args.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    expr.node.print(buf, indent);
                }
                buf.push(')');
            }

            Expr::Int(int) => write!(buf, "{:#x}", int).unwrap(),

            Expr::Str(str) => {
                buf.push('"');
                crate::ast::printer::escape_str_lit(str, buf);
                buf.push('"');
            }

            Expr::BoolAnd(e1, e2) => {
                e1.node.print(buf, indent);
                buf.push_str(" && ");
                e2.node.print(buf, indent);
            }

            Expr::BoolOr(e1, e2) => {
                e1.node.print(buf, indent);
                buf.push_str(" || ");
                e2.node.print(buf, indent);
            }

            Expr::Return(expr) => {
                buf.push_str("return ");
                expr.node.print(buf, indent);
            }

            Expr::Match(MatchExpr {
                scrut,
                alts,
                scrut_ty: _,
                expr_ty: _,
            }) => {
                buf.push_str("match ");
                scrut.node.print(buf, indent);
                buf.push_str(":\n");
                for (i, Alt { pat, guard, rhs }) in alts.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[0..indent as usize + 2]);
                    pat.node.print(buf);
                    if let Some(guard) = guard {
                        buf.push_str(" if ");
                        guard.node.print(buf, indent + 8);
                    }
                    buf.push_str(":\n");
                    for stmt in rhs {
                        buf.push_str(&INDENTS[0..indent as usize + 4]);
                        stmt.node.print(buf, indent + 4);
                    }
                }
            }

            Expr::If(IfExpr {
                branches,
                else_branch,
                expr_ty: _,
            }) => {
                buf.push_str("if ");
                branches[0].0.node.print(buf, indent);
                buf.push_str(":\n");
                for stmt in &branches[0].1 {
                    buf.push_str(&INDENTS[0..indent as usize + 2]);
                    stmt.node.print(buf, indent + 2);
                }
                for branch in &branches[1..] {
                    buf.push('\n');
                    buf.push_str(&INDENTS[0..indent as usize]);
                    buf.push_str("elif ");
                    branch.0.node.print(buf, indent);
                    buf.push_str(":\n");
                    for stmt in &branch.1 {
                        buf.push_str(&INDENTS[0..indent as usize + 2]);
                        stmt.node.print(buf, indent + 2);
                    }
                }
                if let Some(else_branch) = else_branch {
                    buf.push('\n');
                    buf.push_str(&INDENTS[0..indent as usize]);
                    buf.push_str("else:\n");
                    for stmt in else_branch {
                        buf.push_str(&INDENTS[0..indent as usize + 2]);
                        stmt.node.print(buf, indent + 2);
                    }
                }
            }

            Expr::ClosureAlloc(idx) => write!(buf, "closure{}", idx.0).unwrap(),

            Expr::Is(IsExpr {
                expr,
                pat,
                expr_ty: _,
            }) => {
                buf.push('(');
                expr.node.print(buf, indent);
                buf.push_str(" is ");
                pat.node.print(buf);
                buf.push(')');
            }

            Expr::Do(body, _) => {
                buf.push_str("do:\n");
                for stmt in body.iter() {
                    buf.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buf, indent + 4);
                }
            }

            Expr::Variant(expr) => {
                buf.push('~');
                expr.node.print(buf, indent);
            }
        }
    }
}

impl Pat {
    pub fn print(&self, buf: &mut String) {
        match self {
            Pat::Var(idx) => write!(buf, "local{}", idx.0).unwrap(),

            Pat::Con(ConPat { con, fields }) => {
                write!(buf, "con{}(", con.0).unwrap();
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    field.node.print(buf);
                }
                buf.push(')');
            }

            Pat::Ignore => {
                buf.push('_');
            }

            Pat::Str(str) => {
                buf.push('"');
                crate::ast::printer::escape_str_lit(str, buf);
                buf.push('"');
            }

            Pat::Char(char) => {
                buf.push('\'');
                crate::ast::printer::escape_char_lit(*char, buf);
                buf.push('\'');
            }

            Pat::Or(p1, p2) => {
                p1.node.print(buf);
                buf.push_str(" | ");
                p2.node.print(buf);
            }

            Pat::Variant(p) => {
                buf.push('~');
                p.node.print(buf);
            }
        }
    }
}

fn print_ty_args(ty_args: &[mono::Type], buf: &mut String) {
    if ty_args.is_empty() {
        return;
    }

    buf.push('[');
    for (i, ty_arg) in ty_args.iter().enumerate() {
        if i != 0 {
            buf.push_str(", ");
        }
        ty_arg.print(buf);
    }
    buf.push(']');
}

const INDENTS: &str = "                                                  ";
