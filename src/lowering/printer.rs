use crate::lowering::*;
use crate::mono_ast as mono;

use std::fmt::Write;

pub fn print_pgm(pgm: &LoweredPgm) {
    let mut s = String::new();
    pgm.print(&mut s);
    println!("{s}");
}

impl LoweredPgm {
    pub fn print(&self, buffer: &mut String) {
        for (heap_obj_idx, heap_obj) in self.heap_objs.iter().enumerate() {
            write!(buffer, "heap_obj{heap_obj_idx}: ").unwrap();
            match heap_obj {
                HeapObj::Builtin(builtin) => write!(buffer, "{builtin:?}").unwrap(),

                HeapObj::Source(SourceConDecl {
                    name,
                    idx,
                    ty_args,
                    fields,
                    alloc: _,
                }) => {
                    assert_eq!(idx.0 as usize, heap_obj_idx);
                    buffer.push_str(name.as_str());
                    print_ty_args(ty_args, buffer);
                    buffer.push('(');
                    match fields {
                        ConFields::Named(items) => {
                            for (i, (field_name, field_ty)) in items.iter().enumerate() {
                                if i != 0 {
                                    buffer.push_str(", ");
                                }
                                buffer.push_str(field_name.as_str());
                                buffer.push_str(": ");
                                field_ty.print(buffer);
                            }
                        }
                        ConFields::Unnamed(items) => {
                            for (i, field_ty) in items.iter().enumerate() {
                                if i != 0 {
                                    buffer.push_str(", ");
                                }
                                field_ty.print(buffer);
                            }
                        }
                    }
                    buffer.push(')');
                }

                HeapObj::Record(record) => write!(buffer, "{record:?}").unwrap(),
            }
            buffer.push('\n');
        }

        buffer.push('\n');

        for (fun_idx, fun) in self.funs.iter().enumerate() {
            write!(buffer, "fun{fun_idx}: ").unwrap();
            match fun {
                Fun::Builtin(builtin) => write!(buffer, "{builtin:?}").unwrap(),

                Fun::Source(SourceFunDecl {
                    parent_ty,
                    name,
                    idx,
                    ty_args,
                    locals,
                    params,
                    return_ty,
                    exceptions,
                    body,
                }) => {
                    assert_eq!(idx.0 as usize, fun_idx);
                    if let Some(parent_ty) = parent_ty {
                        write!(buffer, "{}.", parent_ty.node).unwrap();
                    }
                    buffer.push_str(name.node.as_str());
                    print_ty_args(ty_args, buffer);
                    buffer.push('\n');

                    buffer.push_str("  locals: ");
                    for (i, local) in locals.iter().enumerate() {
                        if i != 0 {
                            buffer.push_str(", ");
                        }
                        write!(buffer, "{}: {}: ", i, local.name).unwrap();
                        local.ty.print(buffer);
                    }
                    buffer.push('\n');

                    buffer.push_str("  params: ");
                    for (i, arg) in params.iter().enumerate() {
                        if i != 0 {
                            buffer.push_str(", ");
                        }
                        arg.print(buffer);
                    }
                    buffer.push('\n');

                    buffer.push_str("  return_ty: ");
                    return_ty.print(buffer);
                    buffer.push('\n');

                    buffer.push_str("  exceptions: ");
                    exceptions.print(buffer);
                    buffer.push('\n');
                    buffer.push('\n');

                    for stmt in body {
                        buffer.push_str(&INDENTS[0..2]);
                        stmt.node.print(buffer, 2);
                    }
                }
            }
            buffer.push('\n');
        }

        for (
            closure_idx,
            Closure {
                idx,
                locals,
                fvs,
                params,
                body,
                loc: _,
            },
        ) in self.closures.iter().enumerate()
        {
            assert_eq!(idx.0 as usize, closure_idx);
            writeln!(buffer, "closure{closure_idx}:").unwrap();

            buffer.push_str("  locals: ");
            for (i, LocalInfo { name, ty }) in locals.iter().enumerate() {
                if i != 0 {
                    buffer.push_str(", ");
                }
                buffer.push_str(name.as_str());
                buffer.push_str(": ");
                ty.print(buffer);
            }
            buffer.push('\n');

            buffer.push_str("  fvs: ");
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
                    buffer.push_str(", ");
                }
                write!(buffer, "{}(alloc={}, use={})", id, alloc_idx.0, use_idx.0).unwrap();
            }
            buffer.push('\n');

            buffer.push_str("  params: ");
            for (i, arg) in params.iter().enumerate() {
                if i != 0 {
                    buffer.push_str(", ");
                }
                arg.print(buffer);
            }
            buffer.push('\n');
            buffer.push('\n');

            for stmt in body {
                buffer.push_str(&INDENTS[0..2]);
                stmt.node.print(buffer, 2);
            }

            buffer.push('\n');
        }
    }
}

impl Ty {
    pub fn print(&self, buffer: &mut String) {
        self.mono_ty.print(buffer);
        write!(buffer, "#{:?}", self.repr).unwrap();
    }
}

impl Stmt {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            Stmt::Let(LetStmt { lhs, rhs }) => {
                buffer.push_str("let ");
                lhs.node.print(buffer);
                buffer.push_str(" = ");
                rhs.node.print(buffer, indent);
            }

            Stmt::Assign(AssignStmt { lhs, rhs, op }) => {
                lhs.node.print(buffer, indent);
                buffer.push(' ');
                buffer.push_str(match op {
                    AssignOp::Eq => "=",
                    AssignOp::PlusEq => "+=",
                    AssignOp::MinusEq => "-=",
                    AssignOp::StarEq => "*=",
                    AssignOp::CaretEq => "^=",
                });
                buffer.push(' ');
                rhs.node.print(buffer, indent);
            }

            Stmt::Expr(expr) => expr.node.print(buffer, indent),

            Stmt::For(ForStmt {
                pat,
                expr,
                body,
                next_method: _,
                option_some_con: _,
            }) => {
                buffer.push_str("for ");
                pat.node.print(buffer);
                buffer.push_str(" in ");
                expr.node.print(buffer, indent);
                buffer.push_str(":\n");
                for stmt in body {
                    buffer.push_str(&INDENTS[0..(indent + 2) as usize]);
                    stmt.node.print(buffer, indent + 2);
                }
            }

            Stmt::While(WhileStmt { label, cond, body }) => {
                if let Some(label) = label {
                    write!(buffer, "{label}: ").unwrap();
                }
                buffer.push_str("while ");
                cond.node.print(buffer, indent);
                buffer.push_str(":\n");
                for stmt in body {
                    buffer.push_str(&INDENTS[0..(indent + 2) as usize]);
                    stmt.node.print(buffer, indent + 2);
                }
            }

            Stmt::Break { label, level: _ } => match label {
                Some(label) => write!(buffer, "break {label}").unwrap(),
                None => buffer.push_str("break"),
            },

            Stmt::Continue { label, level: _ } => match label {
                Some(label) => write!(buffer, "continue {label}").unwrap(),
                None => buffer.push_str("continue"),
            },
        }

        buffer.push('\n');
    }
}

impl Expr {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            Expr::LocalVar(idx) => write!(buffer, "local{}", idx.0).unwrap(),

            Expr::TopVar(idx) => write!(buffer, "fun{}", idx.0).unwrap(),

            Expr::Constr(idx) => write!(buffer, "con{}", idx.0).unwrap(),

            Expr::FieldSelect(FieldSelectExpr { object, field }) => {
                object.node.print(buffer, indent);
                buffer.push('.');
                buffer.push_str(field);
            }

            Expr::MethodSelect(MethodSelectExpr { object, fun_idx }) => {
                object.node.print(buffer, indent);
                write!(buffer, ".fun{}", fun_idx.0).unwrap();
            }

            Expr::AssocFnSelect(idx) => write!(buffer, "assocfun{}", idx.0).unwrap(),

            Expr::Call(CallExpr { fun, args }) => {
                fun.node.print(buffer, indent);
                buffer.push('(');
                for (i, CallArg { name, expr }) in args.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    expr.node.print(buffer, indent);
                }
                buffer.push(')');
            }

            Expr::Int(int) => mono::Expr::Int(int.clone()).print(buffer, 0),

            Expr::String(parts) => {
                buffer.push('"');
                for part in parts {
                    match part {
                        StringPart::Str(str) => buffer.push_str(str), // TODO: escaping
                        StringPart::Expr(expr) => {
                            buffer.push('`');
                            expr.node.print(buffer, indent);
                            buffer.push('`');
                        }
                    }
                }
                buffer.push('"');
            }

            Expr::Char(char) => {
                buffer.push('\'');
                buffer.push(*char); // TODO: escaping
                buffer.push('\'');
            }

            Expr::BoolNot(e) => {
                buffer.push('!');
                e.node.print(buffer, indent);
            }

            Expr::BoolAnd(e1, e2) => {
                e1.node.print(buffer, indent);
                buffer.push_str(" && ");
                e2.node.print(buffer, indent);
            }

            Expr::BoolOr(e1, e2) => {
                e1.node.print(buffer, indent);
                buffer.push_str(" || ");
                e2.node.print(buffer, indent);
            }

            Expr::Record(RecordExpr { fields, idx }) => {
                write!(buffer, "rec{}(", idx.0).unwrap();
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = &field.name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    field.node.node.print(buffer, indent);
                }
                buffer.push(')');
            }

            Expr::Return(expr) => {
                buffer.push_str("return ");
                expr.node.print(buffer, indent);
            }

            Expr::Match(MatchExpr { scrutinee, alts }) => {
                buffer.push_str("match ");
                scrutinee.node.print(buffer, indent);
                buffer.push_str(":\n");
                for (
                    i,
                    Alt {
                        pattern,
                        guard,
                        rhs,
                    },
                ) in alts.iter().enumerate()
                {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..indent as usize + 2]);
                    pattern.node.print(buffer);
                    if let Some(guard) = guard {
                        buffer.push_str(" if ");
                        guard.node.print(buffer, indent + 8);
                    }
                    buffer.push_str(":\n");
                    for stmt in rhs {
                        buffer.push_str(&INDENTS[0..indent as usize + 4]);
                        stmt.node.print(buffer, indent + 4);
                    }
                }
            }

            Expr::If(IfExpr {
                branches,
                else_branch,
            }) => {
                buffer.push_str("if ");
                branches[0].0.node.print(buffer, indent);
                buffer.push_str(":\n");
                for stmt in &branches[0].1 {
                    buffer.push_str(&INDENTS[0..indent as usize + 2]);
                    stmt.node.print(buffer, indent + 2);
                }
                for branch in &branches[1..] {
                    buffer.push('\n');
                    buffer.push_str(&INDENTS[0..indent as usize]);
                    buffer.push_str("elif ");
                    branch.0.node.print(buffer, indent);
                    buffer.push_str(":\n");
                    for stmt in &branch.1 {
                        buffer.push_str(&INDENTS[0..indent as usize + 2]);
                        stmt.node.print(buffer, indent + 2);
                    }
                }
                if let Some(else_branch) = else_branch {
                    buffer.push('\n');
                    buffer.push_str(&INDENTS[0..indent as usize]);
                    buffer.push_str("else:\n");
                    for stmt in else_branch {
                        buffer.push_str(&INDENTS[0..indent as usize + 2]);
                        stmt.node.print(buffer, indent + 2);
                    }
                }
            }

            Expr::ClosureAlloc(idx) => write!(buffer, "closure{}", idx.0).unwrap(),

            Expr::Is(IsExpr { expr, pat }) => {
                buffer.push('(');
                expr.node.print(buffer, indent);
                buffer.push_str(" is ");
                pat.node.print(buffer);
                buffer.push(')');
            }

            Expr::Do(body) => {
                buffer.push_str("do:\n");
                for stmt in body.iter() {
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                    buffer.push('\n');
                }
            }
        }
    }
}

impl Pat {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Pat::Var(idx) => write!(buffer, "local{}", idx.0).unwrap(),

            Pat::Constr(ConstrPattern { constr, fields }) => {
                write!(buffer, "con{}(", constr.0).unwrap();
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = &field.name {
                        write!(buffer, "{name}: ").unwrap();
                    }
                    field.node.node.print(buffer);
                }
                buffer.push(')');
            }

            Pat::Record(RecordPattern { fields, idx }) => {
                write!(buffer, "rec{}(", idx.0).unwrap();
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = &field.name {
                        write!(buffer, "{name}: ").unwrap();
                    }
                    field.node.node.print(buffer);
                }
                buffer.push(')');
            }

            Pat::Ignore => {
                buffer.push('_');
            }

            Pat::Str(str) => {
                buffer.push('"');
                buffer.push_str(str); // TOOD: escaping
                buffer.push('"');
            }

            Pat::Char(char) => {
                buffer.push('\'');
                buffer.push(*char); // TODO: escaping
                buffer.push('\'');
            }

            Pat::Or(p1, p2) => {
                p1.node.print(buffer);
                buffer.push_str(" | ");
                p2.node.print(buffer);
            }
        }
    }
}

fn print_ty_args(ty_args: &[mono::Type], buffer: &mut String) {
    if ty_args.is_empty() {
        return;
    }

    buffer.push('[');
    for (i, ty_arg) in ty_args.iter().enumerate() {
        if i != 0 {
            buffer.push_str(", ");
        }
        ty_arg.print(buffer);
    }
    buffer.push(']');
}

const INDENTS: &str = "                                                  ";
