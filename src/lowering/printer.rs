use crate::indenting_printer::Printer;
use crate::lowering::*;
use crate::mono_ast as mono;
use crate::utils::loc_display;

use std::fmt::Write;

pub fn print_pgm(pgm: &LoweredPgm) {
    let mut p = Printer::new();
    pgm.print(&mut p);
    println!("{}", p.as_str());
}

impl LoweredPgm {
    pub fn print(&self, p: &mut Printer) {
        for (heap_obj_idx, heap_obj) in self.heap_objs.iter().enumerate() {
            write!(p, "heap_obj{heap_obj_idx}: ").unwrap();
            match heap_obj {
                HeapObj::Builtin(builtin) => write!(p, "{builtin:?}").unwrap(),

                HeapObj::Source(SourceConDecl {
                    name,
                    idx,
                    ty_args,
                    fields,
                    sum: _,
                    value: _,
                }) => {
                    assert_eq!(idx.0 as usize, heap_obj_idx);
                    p.str(name.as_str());
                    print_ty_args(ty_args, p);
                    p.char('(');
                    p.sep(fields.iter(), ", ", |p, field_ty| {
                        write!(p, "{field_ty}").unwrap()
                    });
                    p.char(')');
                }

                HeapObj::Record(record) => write!(p, "{record:?}").unwrap(),

                HeapObj::Variant(variant) => write!(p, "{variant:?}").unwrap(),
            }
            p.nl();
        }

        p.nl();

        for (fun_idx, fun) in self.funs.iter().enumerate() {
            match &fun.body {
                FunBody::Builtin(builtin) => {
                    write!(p, "// {builtin:?}").unwrap();
                    p.nl();
                    write!(p, "fun{fun_idx}: {builtin:?}").unwrap();
                    p.nl();
                }

                FunBody::Source(SourceFunDecl { locals, body }) => {
                    assert_eq!(fun.idx.0 as usize, fun_idx);
                    write!(p, "// {}", loc_display(&fun.name.loc)).unwrap();
                    p.nl();
                    write!(p, "fun{fun_idx}: ").unwrap();
                    if let Some(parent_ty) = &fun.parent_ty {
                        write!(p, "{}.", parent_ty.node).unwrap();
                    }
                    p.str(fun.name.node.as_str());
                    print_ty_args(&fun.ty_args, p);
                    p.indented(|p| {
                        p.nl();
                        p.str("locals: ");
                        p.sep(locals.iter().enumerate(), ", ", |p, (i, local)| {
                            write!(p, "{}: {}: {}", i, local.name, local.ty).unwrap();
                        });
                        p.nl();
                        p.str("params: ");
                        p.sep(fun.params.iter(), ", ", |p, arg| {
                            write!(p, "{arg}").unwrap()
                        });
                        p.nl();
                        write!(p, "return_ty: {}", fun.return_ty).unwrap();
                        p.nl();
                        write!(p, "exceptions: {}", fun.exceptions).unwrap();
                        p.nl();
                        p.nl();
                        for stmt in body {
                            stmt.node.print(p);
                        }
                    });
                    p.nl();
                }
            }
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
            write!(p, "// {}", loc_display(loc)).unwrap();
            p.nl();
            write!(p, "closure{closure_idx}:").unwrap();
            p.indented(|p| {
                p.nl();
                p.str("locals: ");
                p.sep(locals.iter(), ", ", |p, LocalInfo { name, ty }| {
                    write!(p, "{}: {}", name, ty).unwrap();
                });
                p.nl();
                p.str("fvs: ");
                p.sep(
                    fvs.iter(),
                    ", ",
                    |p,
                     ClosureFv {
                         id,
                         alloc_idx,
                         use_idx,
                     }| {
                        write!(p, "{}(alloc={}, use={})", id, alloc_idx.0, use_idx.0).unwrap();
                    },
                );
                p.nl();
                p.str("params: ");
                p.sep(params.iter(), ", ", |p, arg| write!(p, "{arg}").unwrap());
                p.nl();
                write!(p, "return_ty: {return_ty}").unwrap();
                p.nl();
                write!(p, "exceptions: {exceptions}").unwrap();
                p.nl();
                p.nl();
                for stmt in body {
                    stmt.node.print(p);
                }
            });
            p.nl();
        }
    }
}

impl Stmt {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Stmt::Let(LetStmt {
                lhs,
                rhs,
                rhs_ty: _,
            }) => {
                p.str("let ");
                lhs.node.print(p);
                p.str(" = ");
                rhs.node.print(p);
            }

            Stmt::Assign(AssignStmt { lhs, rhs }) => {
                lhs.node.print(p);
                p.str(" = ");
                rhs.node.print(p);
            }

            Stmt::Expr(expr) => expr.print(p),

            Stmt::While(WhileStmt { label, cond, body }) => {
                if let Some(label) = label {
                    write!(p, "{label}: ").unwrap();
                }
                p.str("while ");
                cond.node.print(p);
                p.char(':');
                p.indented(|p| {
                    p.nl();
                    for stmt in body {
                        stmt.node.print(p);
                    }
                });
            }

            Stmt::Break { label, level: _ } => match label {
                Some(label) => write!(p, "break {label}").unwrap(),
                None => p.str("break"),
            },

            Stmt::Continue { label, level: _ } => match label {
                Some(label) => write!(p, "continue {label}").unwrap(),
                None => p.str("continue"),
            },
        }

        p.nl();
    }
}

impl Expr {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Expr::LocalVar(idx) => write!(p, "local{}", idx.as_usize()).unwrap(),

            Expr::Fun(idx) => write!(p, "fun{}", idx.as_usize()).unwrap(),

            Expr::Con(idx) => write!(p, "con{}", idx.as_usize()).unwrap(),

            Expr::ConAlloc {
                con_idx,
                args,
                arg_tys: _,
                ret_ty: _,
            } => {
                write!(p, "con{}", con_idx.as_usize()).unwrap();
                p.char('(');
                p.sep(args.iter(), ", ", |p, expr| expr.node.print(p));
                p.char(')');
            }

            Expr::FieldSel(FieldSelExpr {
                object,
                field,
                idx: _,
                object_ty: _,
            }) => {
                object.node.print(p);
                p.char('.');
                p.str(field);
            }

            Expr::Call(CallExpr {
                fun,
                args,
                fun_ty: _,
            }) => {
                fun.node.print(p);
                p.char('(');
                p.sep(args.iter(), ", ", |p, expr| expr.node.print(p));
                p.char(')');
            }

            Expr::Int(int) => write!(p, "{:#x}", int).unwrap(),

            Expr::Str(str) => {
                p.char('"');
                crate::ast::printer::escape_str_lit(str, p);
                p.char('"');
            }

            Expr::BoolAnd(e1, e2) => {
                e1.node.print(p);
                p.str(" && ");
                e2.node.print(p);
            }

            Expr::BoolOr(e1, e2) => {
                e1.node.print(p);
                p.str(" || ");
                e2.node.print(p);
            }

            Expr::Return(expr, _) => {
                p.str("return ");
                expr.node.print(p);
            }

            Expr::Match(MatchExpr {
                scrutinee,
                alts,
                scrut_ty: _,
                ty: _,
            }) => {
                p.str("match ");
                scrutinee.node.print(p);
                p.char(':');
                p.indented(|p| {
                    for Alt { pat, guard, rhs } in alts.iter() {
                        p.nl();
                        pat.node.print(p);
                        if let Some(guard) = guard {
                            p.str(" if ");
                            guard.node.print(p);
                        }
                        p.char(':');
                        p.indented(|p| {
                            p.nl();
                            for stmt in rhs {
                                stmt.node.print(p);
                            }
                        });
                    }
                });
            }

            Expr::If(IfExpr {
                branches,
                else_branch,
                ty: _,
            }) => {
                p.str("if ");
                branches[0].0.node.print(p);
                p.char(':');
                p.indented(|p| {
                    p.nl();
                    for stmt in &branches[0].1 {
                        stmt.node.print(p);
                    }
                });
                for branch in &branches[1..] {
                    p.nl();
                    p.str("elif ");
                    branch.0.node.print(p);
                    p.char(':');
                    p.indented(|p| {
                        p.nl();
                        for stmt in &branch.1 {
                            stmt.node.print(p);
                        }
                    });
                }
                if let Some(else_branch) = else_branch {
                    p.nl();
                    p.str("else:");
                    p.indented(|p| {
                        p.nl();
                        for stmt in else_branch {
                            stmt.node.print(p);
                        }
                    });
                }
            }

            Expr::ClosureAlloc(idx) => write!(p, "closure{}", idx.0).unwrap(),

            Expr::Is(IsExpr {
                expr,
                pat,
                expr_ty: _,
            }) => {
                p.char('(');
                expr.node.print(p);
                p.str(" is ");
                pat.node.print(p);
                p.char(')');
            }

            Expr::Do(body, _) => {
                p.str("do:");
                p.indented(|p| {
                    p.indented(|p| {
                        p.nl();
                        for stmt in body.iter() {
                            stmt.node.print(p);
                        }
                    });
                });
            }

            Expr::Variant {
                expr,
                expr_ty: _,
                variant_ty: _,
            } => {
                p.char('~');
                expr.node.print(p);
            }

            Expr::InlineC { parts } => todo!(),
        }
    }
}

impl Pat {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Pat::Var(VarPat {
                idx,
                original_ty: _,
            }) => write!(p, "local{}", idx.0).unwrap(),

            Pat::Con(ConPat { con, fields, rest }) => {
                write!(p, "con{}(", con.0).unwrap();
                p.sep(fields.iter(), ", ", |p, field| field.node.print(p));
                match rest {
                    RestPat::No => {}
                    RestPat::Ignore => {
                        if !fields.is_empty() {
                            p.str(", ");
                        }
                        p.str("..");
                    }
                    RestPat::Bind {
                        var,
                        rest_con,
                        rest_field_indices,
                    } => {
                        if !fields.is_empty() {
                            p.str(", ");
                        }
                        write!(
                            p,
                            "..local{} [con={}, fields={:?}]",
                            var.idx.0, rest_con.0, rest_field_indices
                        )
                        .unwrap();
                    }
                }
                p.char(')');
            }

            Pat::Ignore => {
                p.char('_');
            }

            Pat::Str(str) => {
                p.char('"');
                crate::ast::printer::escape_str_lit(str, p);
                p.char('"');
            }

            Pat::Char(char) => {
                p.char('\'');
                crate::ast::printer::escape_char_lit(*char, p);
                p.char('\'');
            }

            Pat::Or(p1, p2) => {
                p1.node.print(p);
                p.str(" | ");
                p2.node.print(p);
            }

            Pat::Variant {
                pat,
                variant_ty: _,
                pat_ty: _,
            } => {
                p.char('~');
                pat.node.print(p);
            }
        }
    }
}

fn print_ty_args(ty_args: &[mono::Type], p: &mut Printer) {
    if ty_args.is_empty() {
        return;
    }

    p.char('[');
    p.sep(ty_args.iter(), ", ", |p, ty_arg| {
        write!(p, "{ty_arg}").unwrap()
    });
    p.char(']');
}
