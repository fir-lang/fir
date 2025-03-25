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
            Stmt::Let(_) => todo!(),

            Stmt::Assign(_) => todo!(),

            Stmt::Expr(expr) => expr.node.print(buffer),

            Stmt::For(_) => todo!(),

            Stmt::While(_) => todo!(),

            Stmt::WhileLet(_) => todo!(),

            Stmt::Break { label: _, level: _ } => todo!(),

            Stmt::Continue { label: _, level: _ } => todo!(),
        }
    }
}

impl Expr {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Expr::LocalVar(_) => todo!(),

            Expr::TopVar(_) => todo!(),

            Expr::Constr(_) => todo!(),

            Expr::FieldSelect(_) => todo!(),

            Expr::MethodSelect(_) => todo!(),

            Expr::AssocFnSelect(_) => todo!(),

            Expr::Call(_) => todo!(),

            Expr::Int(_) => todo!(),

            Expr::String(_) => todo!(),

            Expr::Char(_) => todo!(),

            Expr::Self_ => todo!(),

            Expr::BoolAnd(_, _) => todo!(),

            Expr::BoolOr(_, _) => todo!(),

            Expr::Record(_) => todo!(),

            Expr::Variant(_) => todo!(),

            Expr::Return(_) => todo!(),

            Expr::Match(_) => todo!(),

            Expr::If(_) => todo!(),

            Expr::ClosureAlloc(_) => todo!(),
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
