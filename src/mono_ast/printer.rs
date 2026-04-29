use crate::indenting_printer::Printer;
use crate::mono_ast::*;

use std::fmt::Write;

pub fn print_pgm(pgm: &MonoPgm) {
    let mut p = Printer::new();
    pgm.print(&mut p);
    println!("{}", p.as_str());
}

impl MonoPgm {
    pub fn print(&self, p: &mut Printer) {
        for ty_arg_map in self.ty.values() {
            for (ty_args, ty_decl) in ty_arg_map.iter() {
                p.str("type ");
                p.str(&ty_decl.name);
                print_ty_args(ty_args, p);
                if let Some(rhs) = &ty_decl.rhs {
                    rhs.print(p);
                }
                p.nl();
                p.nl();
            }
        }

        for fun_insts in self.funs.values() {
            for (ty_args, fun) in fun_insts.iter() {
                fun.print(p, ty_args);
                p.nl();
                p.nl();
            }
        }

        for ty_arg_map in self
            .associated
            .values()
            .flat_map(|method_map| method_map.values())
        {
            for (ty_args, fun) in ty_arg_map.iter() {
                fun.print(p, ty_args);
                p.nl();
                p.nl();
            }
        }
    }
}

impl TypeDecl {
    pub fn print(&self, p: &mut Printer) {
        p.str("type ");
        p.str(&self.name);

        if let Some(rhs) = &self.rhs {
            rhs.print(p);
        }
    }
}

impl TypeDeclRhs {
    pub fn print(&self, p: &mut Printer) {
        match self {
            TypeDeclRhs::Sum(cons) => {
                p.char(':');
                p.indented(|p| {
                    for con in cons.iter() {
                        p.nl();
                        p.str(&con.name);
                        print_con_fields(&con.fields, p);
                    }
                });
            }

            TypeDeclRhs::Product(fields) => {
                print_con_fields(fields, p);
            }
        }
    }
}

fn print_con_fields(fields: &ConFields, p: &mut Printer) {
    match fields {
        ConFields::Empty => {}

        ConFields::Named(fields) => {
            p.char('(');
            p.indented(|p| {
                for (field_name, field_ty) in fields.iter() {
                    p.nl();
                    p.str(field_name);
                    p.str(": ");
                    field_ty.print(p);
                    p.char(',');
                }
            });
            p.nl();
            p.char(')');
        }

        ConFields::Unnamed(fields) => {
            p.char('(');
            p.sep(fields.iter(), ", ", |p, field_ty| field_ty.print(p));
            p.char(')');
        }
    }
}

impl FunDecl {
    pub fn print(&self, p: &mut Printer, ty_args: &[Type]) {
        self.sig.print(&self.parent_ty, &self.name.node, ty_args, p);
        if let Some(body) = &self.body {
            p.char(':');
            p.indented(|p| {
                for stmt in body.iter() {
                    p.nl();
                    stmt.node.print(p);
                }
            });
        }
    }
}

impl Type {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Type::Named(ty) => {
                ty.print(p);
            }

            Type::Record { fields } => {
                p.char('(');
                p.sep(fields.iter(), ", ", |p, (field_name, field_ty)| {
                    p.str(field_name);
                    p.str(": ");
                    field_ty.print(p);
                });
                p.char(')');
            }

            Type::Variant { alts } => {
                p.char('[');
                p.sep(alts.values(), ", ", |p, ty| ty.print(p));
                p.char(']');
            }

            Type::Fn(FnType { args, ret, exn }) => {
                p.str("Fn(");
                match args {
                    FunArgs::Positional(args) => {
                        p.sep(args.iter(), ", ", |p, arg| arg.print(p));
                    }
                    FunArgs::Named(args) => {
                        p.sep(args.iter(), ", ", |p, (name, ty)| {
                            p.str(name);
                            p.str(": ");
                            ty.print(p);
                        });
                    }
                }
                p.char(')');
                p.char(' ');
                ret.print(p);
                p.str(" / ");
                exn.print(p);
            }
        }
    }
}

impl NamedType {
    pub fn print(&self, p: &mut Printer) {
        p.str(&self.name);
        if !self.args.is_empty() {
            p.char('[');
            p.sep(self.args.iter(), ", ", |p, arg| arg.print(p));
            p.char(']');
        }
    }
}

impl FunSig {
    pub fn print(
        &self,
        parent_ty: &Option<L<Name>>,
        name: &Name,
        ty_args: &[Type],
        p: &mut Printer,
    ) {
        if let Some(parent_ty) = parent_ty {
            p.str(&parent_ty.node);
            p.char('.');
        }
        p.str(name);
        print_ty_args(ty_args, p);
        p.char('(');
        p.sep(self.params.iter(), ", ", |p, (param_name, param_ty)| {
            p.str(param_name);
            p.str(": ");
            param_ty.node.print(p);
        });
        p.char(')');
        if let Some(ret_ty) = &self.return_ty {
            p.char(' ');
            ret_ty.node.print(p);
        }
        if let Some(exn) = &self.exceptions {
            p.str(" / ");
            exn.node.print(p);
        }
    }
}

impl Stmt {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Stmt::Break { label, level: _ } => {
                p.str("break");
                if let Some(label) = label {
                    p.str(" \'");
                    p.str(label);
                }
            }

            Stmt::Continue { label, level: _ } => {
                p.str("continue");
                if let Some(label) = label {
                    p.str(" \'");
                    p.str(label);
                }
            }

            Stmt::Let(LetStmt { lhs, rhs }) => {
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
                    p.char('\'');
                    p.str(label);
                    p.str(": ");
                }
                p.str("while ");
                cond.node.print(p);
                p.char(':');
                p.indented(|p| {
                    for stmt in body.iter() {
                        p.nl();
                        stmt.node.print(p);
                    }
                });
            }
        }
    }
}

impl Expr {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Expr::LocalVar(id, _) => {
                p.str(id);
            }

            Expr::TopVar(VarExpr { id, ty_args, ty: _ }) => {
                p.str(id);
                print_ty_args(ty_args, p);
            }

            Expr::FieldSel(FieldSelExpr {
                object,
                field,
                ty: _,
            }) => {
                object.node.print(p);
                p.char('.');
                p.str(field);
            }

            Expr::ConSel(con) => {
                con.print(p);
            }

            Expr::AssocFnSel(AssocFnSelExpr {
                ty_id,
                member,
                ty_args,
                ty: _,
            }) => {
                p.str(ty_id);
                p.char('.');
                p.str(member);
                print_ty_args(ty_args, p);
            }

            Expr::Call(CallExpr {
                fun,
                args,
                splice,
                ty: _,
            }) => {
                let parens = !matches!(
                    &fun.node,
                    Expr::LocalVar(_, _)
                        | Expr::TopVar(_)
                        | Expr::FieldSel(_)
                        | Expr::ConSel(_)
                        | Expr::AssocFnSel(_)
                );
                if parens {
                    p.char('(');
                }
                fun.node.print(p);
                if parens {
                    p.char(')');
                }
                p.char('(');
                p.sep(args.iter(), ", ", |p, CallArg { name, expr }| {
                    if let Some(name) = name {
                        p.str(name);
                        p.str(" = ");
                    }
                    expr.node.print(p);
                });
                if let Some(expr) = splice {
                    if !args.is_empty() {
                        p.str(", ");
                    }
                    expr.node.print(p);
                }
                p.char(')');
            }

            Expr::Int(IntExpr {
                text,
                kind,
                parsed: _,
            }) => {
                p.str(text);
                match kind {
                    Some(IntKind::I64(_)) => p.str("I64"),
                    Some(IntKind::U64(_)) => p.str("U64"),
                    Some(IntKind::I32(_)) => p.str("I32"),
                    Some(IntKind::U32(_)) => p.str("U32"),
                    Some(IntKind::I8(_)) => p.str("I8"),
                    Some(IntKind::U8(_)) => p.str("U8"),
                    None => {}
                }
            }

            Expr::Str(str) => {
                p.char('"');
                crate::ast::printer::escape_str_lit(str, p);
                p.char('"');
            }

            Expr::Char(char) => {
                p.char('\'');
                crate::ast::printer::escape_char_lit(*char, p);
                p.char('\'');
            }

            Expr::BoolOr(left, right) => {
                let left_parens = expr_parens(&left.node);
                let right_parens = expr_parens(&right.node);
                if left_parens {
                    p.char('(');
                }
                left.node.print(p);
                if left_parens {
                    p.char(')');
                }
                p.str(" or ");
                if right_parens {
                    p.char('(');
                }
                right.node.print(p);
                if right_parens {
                    p.char(')');
                }
            }

            Expr::BoolAnd(left, right) => {
                let left_parens = expr_parens(&left.node);
                let right_parens = expr_parens(&right.node);
                if left_parens {
                    p.char('(');
                }
                left.node.print(p);
                if left_parens {
                    p.char(')');
                }
                p.str(" and ");
                if right_parens {
                    p.char('(');
                }
                right.node.print(p);
                if right_parens {
                    p.char(')');
                }
            }

            Expr::Return(expr, _) => {
                p.str("return ");
                expr.node.print(p);
            }

            Expr::Match(MatchExpr {
                scrutinee,
                alts,
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
                            for stmt in rhs.iter() {
                                p.nl();
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
                    for stmt in branches[0].1.iter() {
                        p.nl();
                        stmt.node.print(p);
                    }
                });
                for branch in &branches[1..] {
                    p.nl();
                    p.str("elif ");
                    branch.0.node.print(p);
                    p.char(':');
                    p.indented(|p| {
                        for stmt in branch.1.iter() {
                            p.nl();
                            stmt.node.print(p);
                        }
                    });
                }
                if let Some(else_branch) = else_branch {
                    p.nl();
                    p.str("else:");
                    p.indented(|p| {
                        for stmt in else_branch.iter() {
                            p.nl();
                            stmt.node.print(p);
                        }
                    });
                }
            }

            Expr::Fn(FnExpr { sig, body }) => {
                p.char('\\');
                sig.print(&None, &Name::new_static(""), &[], p);
                p.str(" {");
                p.indented(|p| {
                    for stmt in body.iter() {
                        p.nl();
                        stmt.node.print(p);
                    }
                });
                p.nl();
                p.char('}');
            }

            Expr::Is(IsExpr { expr, pat }) => {
                p.char('(');
                expr.node.print(p);
                p.str(" is ");
                pat.node.print(p);
                p.char(')');
            }

            Expr::Do(body, _) => {
                p.str("do:");
                p.indented(|p| {
                    for stmt in body.iter() {
                        p.nl();
                        stmt.node.print(p);
                    }
                });
            }

            Expr::Record(RecordExpr {
                fields,
                splice,
                ty: _,
            }) => {
                p.char('(');
                p.sep(fields.iter(), ", ", |p, (field_name, field_expr)| {
                    p.str(field_name);
                    p.str(" = ");
                    field_expr.node.print(p);
                });
                if let Some(expr) = splice {
                    if !fields.is_empty() {
                        p.str(", ");
                    }
                    expr.node.print(p);
                }
                p.char(')');
            }

            Expr::Variant(VariantExpr { expr, ty: _ }) => {
                p.char('~');
                expr.node.print(p);
            }

            Expr::InlineC(InlineCExpr { parts, ty }) => todo!(),
        }
    }
}

impl Pat {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Pat::Var(VarPat { var, ty, refined }) => {
                p.str(var);
                p.str(": ");
                ty.print(p);
                if let Some(refined) = refined {
                    p.str(" ~> ");
                    refined.print(p);
                }
            }

            Pat::Con(ConPat { con, fields, rest }) => {
                con.print(p);

                if !fields.is_empty() || !matches!(rest, RestPat::No) {
                    p.char('(');
                    p.sep(fields.iter(), ", ", |p, field| {
                        if let Some(name) = &field.name {
                            p.str(name);
                            p.str(" = ");
                        }
                        field.node.node.print(p);
                    });
                    match rest {
                        RestPat::Ignore => {
                            if !fields.is_empty() {
                                p.str(", ");
                            }
                            p.str("..");
                        }
                        RestPat::Bind(binder) => {
                            if !fields.is_empty() {
                                p.str(", ");
                            }
                            p.str("..");
                            p.str(&binder.var);
                        }
                        RestPat::No => {}
                    }
                    p.char(')');
                }
            }

            Pat::Record(RecordPat { fields, ty, rest }) => {
                p.char('(');
                p.sep(fields.iter(), ", ", |p, Named { name, node }| {
                    if let Some(name) = name {
                        p.str(name);
                        p.str(" = ");
                    }
                    node.node.print(p);
                });
                match rest {
                    RestPat::Ignore => {
                        if !fields.is_empty() {
                            p.str(", ");
                        }
                        p.str("..");
                    }
                    RestPat::Bind(binder) => {
                        if !fields.is_empty() {
                            p.str(", ");
                        }
                        p.str("..");
                        p.str(&binder.var);
                    }
                    RestPat::No => {}
                }
                p.str("): ");
                Type::Record { fields: ty.clone() }.print(p);
            }

            Pat::Ignore => p.char('_'),

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

            Pat::Or(pat1, pat2) => {
                p.char('(');
                pat1.node.print(p);
                p.str(") | (");
                pat2.node.print(p);
                p.char(')');
            }

            Pat::Variant(VariantPat {
                pat,
                variant_ty: _,
                pat_ty: _,
            }) => {
                p.char('~');
                pat.node.print(p);
            }
        }
    }
}

impl Con {
    pub fn print(&self, p: &mut Printer) {
        p.str(&self.ty_id);
        if let Some(con) = &self.con {
            p.char('.');
            p.str(con);
        }
        print_ty_args(&self.ty_args, p);
    }
}

fn expr_parens(expr: &Expr) -> bool {
    !matches!(
        expr,
        Expr::LocalVar(_, _) | Expr::TopVar(_) | Expr::FieldSel(_) | Expr::ConSel(_)
    )
}

fn print_ty_args(args: &[Type], p: &mut Printer) {
    if args.is_empty() {
        return;
    }

    p.char('[');
    p.sep(args.iter(), ", ", |p, ty| write!(p, "{ty}").unwrap());
    p.char(']');
}

use std::fmt::Display;

impl Display for TypeDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for TypeDeclRhs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for FunDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p, &[]);
        f.write_str(p.as_str())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for NamedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for FunSig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&None, &Name::new(""), &[], &mut p);
        f.write_str(p.as_str())
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for Pat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}
