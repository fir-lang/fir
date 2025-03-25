use crate::lowering::*;
use crate::mono_ast as mono;

use std::fmt::Write;

pub fn print_pgm(pgm: &LoweredPgm) {
    let mut s = String::new();
    pgm.print(&mut s);
    println!("{}", s);
}

impl LoweredPgm {
    pub fn print(&self, buffer: &mut String) {
        for (con_idx, con) in self.cons.iter().enumerate() {
            write!(buffer, "Con {}: ", con_idx).unwrap();
            match con {
                Con::Builtin(builtin) => write!(buffer, "{:?}", builtin).unwrap(),

                Con::Source(SourceConDecl {
                    name,
                    idx,
                    ty_args,
                    fields,
                }) => {
                    assert_eq!(idx.0 as usize, con_idx);
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
            }
            buffer.push('\n');
        }

        if !self.cons.is_empty() {
            buffer.push('\n');
        }

        for (fun_idx, fun) in self.funs.iter().enumerate() {
            write!(buffer, "Fun {}: ", fun_idx).unwrap();
            match fun {
                Fun::Bultin(builtin) => write!(buffer, "{:?}", builtin).unwrap(),

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
                        write!(buffer, "{}: ", local.name).unwrap();
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
                        stmt.node.print(buffer, 2);
                    }
                }
            }
            buffer.push('\n');
        }

        if !self.funs.is_empty() {
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
            },
        ) in self.closures.iter().enumerate()
        {
            assert_eq!(idx.0 as usize, closure_idx);
            write!(buffer, "Closure {}:\n", closure_idx).unwrap();

            buffer.push_str("  locals: ");
            for (i, local) in locals.iter().enumerate() {
                if i != 0 {
                    buffer.push_str(", ");
                }
                buffer.push_str(local.as_str());
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
                stmt.node.print(buffer, 2);
            }
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
                buffer.push_str("let");
                lhs.node.print(buffer);
                buffer.push_str(" = ");
                rhs.node.print(buffer);
            }

            Stmt::Assign(AssignStmt { lhs, rhs, op }) => {
                lhs.node.print(buffer);
                buffer.push(' ');
                buffer.push_str(match op {
                    AssignOp::Eq => "=",
                    AssignOp::PlusEq => "+=",
                    AssignOp::MinusEq => "-=",
                    AssignOp::StarEq => "*=",
                });
                buffer.push(' ');
                rhs.node.print(buffer);
            }

            Stmt::Expr(expr) => expr.node.print(buffer),

            Stmt::For(ForStmt {
                label,
                pat,
                expr,
                body,
            }) => {
                if let Some(label) = label {
                    write!(buffer, "{}: ", label).unwrap();
                }
                buffer.push_str("for ");
                pat.node.print(buffer);
                buffer.push_str(" in ");
                expr.node.print(buffer);
                buffer.push_str(":\n");
                for stmt in body {
                    buffer.push_str(&INDENTS[0..(indent + 2) as usize]);
                    stmt.node.print(buffer, indent + 2);
                }
            }

            Stmt::While(WhileStmt { label, cond, body }) => {
                if let Some(label) = label {
                    write!(buffer, "{}: ", label).unwrap();
                }
                buffer.push_str("while ");
                cond.node.print(buffer);
                buffer.push_str(":\n");
                for stmt in body {
                    buffer.push_str(&INDENTS[0..(indent + 2) as usize]);
                    stmt.node.print(buffer, indent + 2);
                }
            }

            Stmt::WhileLet(WhileLetStmt {
                label,
                pat,
                cond,
                body,
            }) => {
                if let Some(label) = label {
                    write!(buffer, "{}: ", label).unwrap();
                }
                buffer.push_str("while let ");
                pat.node.print(buffer);
                buffer.push_str(" = ");
                cond.node.print(buffer);
                buffer.push_str(":\n");
                for stmt in body {
                    buffer.push_str(&INDENTS[0..(indent + 2) as usize]);
                    stmt.node.print(buffer, indent + 2);
                }
            }

            Stmt::Break { label, level: _ } => match label {
                Some(label) => write!(buffer, "break {}", label).unwrap(),
                None => buffer.push_str("break"),
            },

            Stmt::Continue { label, level: _ } => match label {
                Some(label) => write!(buffer, "continue {}", label).unwrap(),
                None => buffer.push_str("continue"),
            },
        }
    }
}

impl Expr {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Expr::LocalVar(idx) => write!(buffer, "local{}", idx.0).unwrap(),

            Expr::TopVar(idx) => write!(buffer, "fun{}", idx.0).unwrap(),

            Expr::Constr(idx) => write!(buffer, "con{}", idx.0).unwrap(),

            Expr::FieldSelect(FieldSelectExpr { object, field }) => {
                object.node.print(buffer);
                buffer.push('.');
                buffer.push_str(field);
            }

            Expr::MethodSelect(MethodSelectExpr { object, fun_idx }) => {
                object.node.print(buffer);
                write!(buffer, ".fun{}", fun_idx.0).unwrap();
            }

            Expr::AssocFnSelect(idx) => write!(buffer, "assocfun{}", idx.0).unwrap(),

            Expr::Call(CallExpr { fun, args }) => {
                fun.node.print(buffer);
                buffer.push('(');
                for (i, CallArg { name, expr }) in args.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    expr.node.print(buffer);
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
                            expr.node.print(buffer);
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

            Expr::Self_ => todo!(),

            Expr::BoolAnd(e1, e2) => {
                e1.node.print(buffer);
                buffer.push_str(" && ");
                e2.node.print(buffer);
            }

            Expr::BoolOr(e1, e2) => {
                e1.node.print(buffer);
                buffer.push_str(" || ");
                e2.node.print(buffer);
            }

            Expr::Record(RecordExpr { fields, idx }) => {
                write!(buffer, "record{}(", idx.0).unwrap();
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = &field.name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    field.node.node.print(buffer);
                }
                buffer.push(')');
            }

            Expr::Variant(VariantExpr { id, fields, idx }) => {
                write!(buffer, "~{}{}", id, idx.0).unwrap();
                if !fields.is_empty() {
                    buffer.push('(');
                    for (i, arg) in fields.iter().enumerate() {
                        if i != 0 {
                            buffer.push_str(", ");
                        }
                        if let Some(name) = &arg.name {
                            buffer.push_str(name);
                            buffer.push_str(" = ");
                        }
                        arg.node.node.print(buffer);
                    }
                    buffer.push(')');
                }
            }

            Expr::Return(expr) => {
                buffer.push_str("return ");
                expr.node.print(buffer);
            }

            Expr::Match(MatchExpr { scrutinee, alts }) => {
                buffer.push_str("match ");
                scrutinee.node.print(buffer);
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
                    buffer.push_str(&INDENTS[0..4]);
                    assert!(guard.is_none()); // TODO
                    pattern.node.print(buffer);
                    buffer.push_str(":\n");
                    for (j, stmt) in rhs.iter().enumerate() {
                        if j != 0 {
                            buffer.push('\n');
                        }
                        buffer.push_str(&INDENTS[0..8]);
                        stmt.node.print(buffer, 8);
                    }
                }
            }

            Expr::If(IfExpr {
                branches,
                else_branch,
            }) => {
                buffer.push_str("if ");
                branches[0].0.node.print(buffer);
                buffer.push_str(":\n");
                for (i, stmt) in branches[0].1.iter().enumerate() {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..4]);
                    stmt.node.print(buffer, 4);
                }
                for branch in &branches[1..] {
                    buffer.push('\n');
                    buffer.push_str("elif ");
                    branch.0.node.print(buffer);
                    buffer.push_str(":\n");
                    for (i, stmt) in branch.1.iter().enumerate() {
                        if i != 0 {
                            buffer.push('\n');
                        }
                        buffer.push_str(&INDENTS[0..4]);
                        stmt.node.print(buffer, 4);
                    }
                }
                if let Some(else_branch) = else_branch {
                    buffer.push('\n');
                    buffer.push_str("else:\n");
                    for (i, stmt) in else_branch.iter().enumerate() {
                        if i != 0 {
                            buffer.push('\n');
                        }
                        buffer.push_str(&INDENTS[0..4]);
                        stmt.node.print(buffer, 4);
                    }
                }
            }

            Expr::ClosureAlloc(idx) => write!(buffer, "closure{}", idx.0).unwrap(),
        }
    }
}

impl Pat {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Pat::Var(idx) => todo!(),

            Pat::Constr(ConstrPattern { constr, fields }) => todo!(),

            Pat::Record(RecordPattern { fields, idx }) => todo!(),

            Pat::Variant(VariantPattern {
                constr,
                fields,
                idx,
            }) => todo!(),

            Pat::Ignore => todo!(),

            Pat::Str(str) => todo!(),

            Pat::Char(char) => todo!(),

            Pat::StrPfx(str, idx) => todo!(),

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
