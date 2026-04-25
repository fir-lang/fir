use crate::indenting_printer::Printer;
use crate::{ast::*, type_checker::RecordOrVariant};

use std::fmt::Write;

impl Module {
    pub fn print(&self) {
        for (i, top_decl) in self.decls.iter().enumerate() {
            if i != 0 {
                println!();
            }
            let mut p = Printer::new();
            top_decl.node.print(&mut p);
            println!("{}", p.as_str());
        }
    }
}

impl TopDecl {
    pub fn print(&self, p: &mut Printer) {
        match self {
            TopDecl::Type(decl) => decl.node.print(p),
            TopDecl::Fun(decl) => decl.node.print(p),
            TopDecl::Import(decl) => decl.node.print(p),
            TopDecl::Trait(decl) => decl.node.print(p),
            TopDecl::Impl(decl) => decl.node.print(p),
        }
    }
}

impl Attribute {
    pub fn print(&self, p: &mut Printer) {
        p.str("#[");
        if let Some(rhs) = &self.lhs {
            rhs.node.print(p);
            p.str(" = ");
        }
        self.expr.node.print(p);
        p.str("]");
        p.nl();
    }
}

impl TypeDecl {
    pub fn print(&self, p: &mut Printer) {
        if let Some(attr) = &self.attr {
            attr.print(p);
        }

        if !self.type_param_kinds.is_empty() {
            p.str("# inferred kinds = ");
            p.sep(
                self.type_params.iter().zip(self.type_param_kinds.iter()),
                ", ",
                |p, (type_param, kind)| {
                    p.str(&type_param.name.node);
                    p.str(": ");
                    write!(p, "{kind}").unwrap();
                },
            );
            p.nl();
        }

        p.str("type ");
        p.str(&self.name);

        if !self.type_params.is_empty() {
            p.char('[');
            p.sep(self.type_params.iter(), ", ", |p, tp| tp.print(p));
            p.char(']');
        }

        if let Some(rhs) = &self.rhs {
            rhs.print(p);
        }
    }
}

impl TypeDeclRhs {
    pub fn print(&self, p: &mut Printer) {
        match self {
            TypeDeclRhs::Sum { cons, extension } => {
                p.char(':');
                p.indented(|p| {
                    for con in cons.iter() {
                        p.nl();
                        p.str(&con.name);
                        print_con_fields(&con.fields, p);
                    }
                    if let Some(ext) = extension {
                        p.nl();
                        p.str("..");
                        ext.node.print(p);
                    }
                });
            }

            TypeDeclRhs::Product(fields) => {
                print_con_fields(fields, p);
            }

            TypeDeclRhs::Synonym(ty) => {
                p.str(" = ");
                ty.node.print(p);
            }
        }
    }
}

fn print_con_fields(fields: &ConFields, p: &mut Printer) {
    match fields {
        ConFields::Empty => {}

        ConFields::Named { fields, extension } => {
            p.char('(');
            p.indented(|p| {
                for (field_name, field_ty) in fields.iter() {
                    p.nl();
                    p.str(field_name);
                    p.str(": ");
                    field_ty.node.print(p);
                    p.char(',');
                }
                if let Some(ext) = extension {
                    p.nl();
                    p.str("..");
                    ext.node.print(p);
                }
            });
            p.nl();
            p.char(')');
        }

        ConFields::Unnamed { fields } => {
            p.char('(');
            p.sep(fields.iter(), ", ", |p, field_ty| field_ty.node.print(p));
            p.char(')');
        }
    }
}

impl FunDecl {
    pub fn print(&self, p: &mut Printer) {
        self.sig.print(&self.parent_ty, &self.name.node, p);
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

impl ImportDecl {
    pub fn print(&self, p: &mut Printer) {
        if let Some(attr) = &self.attr {
            attr.print(p);
        }
        p.str("import [");
        p.indented(|p| {
            for item in self.items.iter() {
                p.nl();
                p.str(&item.path.to_string());
                match &item.import_spec {
                    None => {}
                    Some(ImportSpec::Prefixed { prefix }) => {
                        p.str(" as ");
                        p.str(prefix);
                    }
                    Some(ImportSpec::Selective { names }) => {
                        p.str("/[");
                        p.sep(names.iter(), ", ", |p, name| {
                            p.str(&name.original_name);
                            if name.original_name != name.local_name {
                                p.str(" as ");
                                p.str(&name.local_name);
                            }
                        });
                        p.char(']');
                    }
                }
                p.char(',');
            }
        });
        p.nl();
        p.char(']');
    }
}

impl TraitDecl {
    pub fn print(&self, p: &mut Printer) {
        p.str("trait ");
        p.str(&self.name.node);
        p.char('[');
        p.sep(self.type_params.iter(), ", ", |p, param| param.print(p));
        p.str("]:");
        p.indented(|p| {
            for item in self.items.iter() {
                p.nl();
                item.print(p);
            }
        });
    }
}

impl TypeParam {
    pub fn print(&self, p: &mut Printer) {
        p.str(&self.name.node);
        if let Some(kind) = &self.kind {
            p.str(": ");
            kind.node.print(p);
        }
    }
}

impl TraitDeclItem {
    pub fn print(&self, p: &mut Printer) {
        match self {
            TraitDeclItem::Type {
                name,
                kind,
                default,
            } => {
                p.str("type ");
                p.str(name.node.as_str());
                if let Some(kind) = kind {
                    p.str(": ");
                    kind.node.print(p);
                }
                if let Some(default) = default {
                    p.str(" = ");
                    default.node.print(p);
                }
            }
            TraitDeclItem::Fun(fun) => {
                fun.node.print(p);
            }
        }
    }
}

impl ImplDecl {
    pub fn print(&self, p: &mut Printer) {
        p.str("impl");
        print_context(&self.context, p);
        p.char(' ');
        p.str(&self.trait_.node);
        p.char('[');
        p.sep(self.tys.iter(), ", ", |p, ty| ty.node.print(p));
        p.str("]:");
        p.indented(|p| {
            for (i, item) in self.items.iter().enumerate() {
                if i != 0 {
                    p.nl();
                }
                p.nl();
                item.print(p);
            }
        });
    }
}

impl ImplDeclItem {
    pub fn print(&self, p: &mut Printer) {
        match self {
            ImplDeclItem::Type { assoc_ty, rhs } => {
                p.str("type ");
                p.str(assoc_ty.node.as_str());
                p.str(" = ");
                rhs.node.print(p);
            }
            ImplDeclItem::Fun(fun) => {
                fun.node.print(p);
            }
        }
    }
}

impl Type {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Type::Named(ty) => {
                ty.print(p);
            }

            Type::Var(var) => p.str(var),

            Type::Record {
                fields,
                extension,
                is_row,
            } => {
                if *is_row {
                    p.str("row(");
                } else {
                    p.char('(');
                }
                p.sep(fields.iter(), ", ", |p, (field_name, field_ty)| {
                    p.str(field_name);
                    p.str(": ");
                    field_ty.node.print(p);
                });
                if let Some(extension) = extension {
                    if !fields.is_empty() {
                        p.str(", ");
                    }
                    p.str("..");
                    extension.node.print(p);
                }
                p.char(')');
            }

            Type::Variant {
                alts,
                extension,
                is_row,
            } => {
                if *is_row {
                    p.str("row[");
                } else {
                    p.char('[');
                }
                p.sep(
                    alts.iter(),
                    ", ",
                    |p,
                     NamedType {
                         mod_prefix,
                         name,
                         args,
                     }| {
                        print_mod_prefix(mod_prefix, p);
                        p.str(name);
                        if !args.is_empty() {
                            p.char('(');
                            p.sep(args.iter(), ", ", |p, L { loc: _, node }| {
                                p.str(name);
                                p.str(": ");
                                node.print(p);
                            });
                            p.char(')');
                        }
                    },
                );
                if let Some(ext) = extension {
                    if !alts.is_empty() {
                        p.str(", ");
                    }
                    p.str("..");
                    ext.node.print(p);
                }
                p.char(']');
            }

            Type::Fn(FnType {
                args,
                ret,
                exceptions,
            }) => {
                p.str("Fn(");
                p.sep(args.iter(), ", ", |p, arg| arg.node.print(p));
                p.char(')');
                if let Some(ret) = ret {
                    p.char(' ');
                    ret.node.print(p);
                }
                if let Some(exn) = exceptions {
                    p.str(" / ");
                    exn.node.print(p);
                }
            }

            Type::AssocTySelect { ty, assoc_ty } => {
                ty.node.print(p);
                p.char('.');
                p.str(assoc_ty.as_str());
            }
        }
    }
}

impl NamedType {
    pub fn print(&self, p: &mut Printer) {
        print_mod_prefix(&self.mod_prefix, p);
        p.str(&self.name);
        if !self.args.is_empty() {
            p.char('[');
            p.sep(self.args.iter(), ", ", |p, arg| arg.node.print(p));
            p.char(']');
        }
    }
}

impl Pred {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Pred::Kind { var, kind } => {
                p.str(var);
                if let Some(kind) = kind {
                    p.str(": ");
                    kind.node.print(p);
                }
            }
            Pred::App(type_app) => type_app.print(p),
            Pred::AssocTyEq { ty, assoc_ty, eq } => {
                ty.print(p);
                p.char('.');
                p.str(assoc_ty);
                p.str(" = ");
                eq.node.print(p);
            }
        }
    }
}

impl FunSig {
    pub fn print(&self, parent_ty: &Option<L<Name>>, name: &Name, p: &mut Printer) {
        if let Some(parent_ty) = parent_ty {
            p.str(&parent_ty.node);
            p.char('.');
        }
        p.str(name);
        print_context(&self.context, p);
        p.char('(');
        match &self.self_ {
            SelfParam::No => {}
            SelfParam::Implicit => {
                p.str("self");
                if !self.params.is_empty() {
                    p.str(", ");
                }
            }
            SelfParam::Explicit(ty) => {
                p.str("self: ");
                ty.node.print(p);
                if !self.params.is_empty() {
                    p.str(", ");
                }
            }
        }
        p.sep(self.params.iter(), ", ", |p, (param_name, param_ty)| {
            p.str(param_name);
            if let Some(param_ty) = param_ty {
                p.str(": ");
                param_ty.node.print(p);
            }
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

            Stmt::Let(LetStmt { lhs, ty, rhs }) => {
                p.str("let ");
                lhs.node.print(p);
                if let Some(ty) = ty {
                    p.str(": ");
                    ty.node.print(p);
                }
                p.str(" = ");
                rhs.node.print(p);
            }

            Stmt::Assign(AssignStmt { lhs, rhs, op }) => {
                lhs.node.print(p);
                let op_str = match op {
                    AssignOp::Eq => "=",
                    AssignOp::PlusEq => "+=",
                    AssignOp::MinusEq => "-=",
                    AssignOp::StarEq => "*=",
                    AssignOp::CaretEq => "^=",
                };
                p.char(' ');
                p.str(op_str);
                p.char(' ');
                rhs.node.print(p);
            }

            Stmt::Expr(expr) => expr.print(p),

            Stmt::For(ForStmt {
                label,
                pat,
                item_ast_ty,
                expr,
                body,
            }) => {
                if let Some(label) = label {
                    p.char('\'');
                    p.str(label);
                    p.str(": ");
                }
                p.str("for ");
                pat.node.print(p);
                if let Some(ty) = item_ast_ty {
                    p.str(": ");
                    ty.node.print(p);
                }
                p.str(" in ");
                expr.node.print(p);
                p.char(':');
                p.indented(|p| {
                    for stmt in body.iter() {
                        p.nl();
                        stmt.node.print(p);
                    }
                });
            }

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
            Expr::Var(VarExpr {
                mod_prefix,
                name,
                user_ty_args,
                ty_args,
                inferred_ty: _,
                resolved_id: _,
            }) => {
                print_mod_prefix(mod_prefix, p);
                p.str(name);
                print_user_ty_args(user_ty_args, p);
                print_ty_args(ty_args, p);
            }

            Expr::FieldSel(FieldSelExpr {
                object,
                field,
                user_ty_args,
                inferred_ty: _,
            }) => {
                object.node.print(p);
                p.char('.');
                p.str(field);
                print_user_ty_args(user_ty_args, p);
            }

            Expr::MethodSel(MethodSelExpr {
                object,
                fun,
                ty_args,
                inferred_ty: _,
            }) => {
                object.node.print(p);
                match fun {
                    MethodSelFun::Method { ty_id, method_name } => {
                        p.str(".{");
                        write!(p, "{ty_id}").unwrap();
                        p.str(".}");
                        p.str(method_name);
                    }
                    MethodSelFun::TopLevel { local_name: _, id } => {
                        p.str(".{");
                        write!(p, "{id}").unwrap();
                        p.char('}');
                    }
                    MethodSelFun::Local { name } => {
                        p.char('.');
                        p.str(name);
                    }
                }
                print_ty_args(ty_args, p);
            }

            Expr::ConSel(con) => {
                con.print(p);
            }

            Expr::AssocFnSel(AssocFnSelExpr {
                mod_prefix,
                ty,
                ty_id: _,
                ty_user_ty_args,
                member,
                user_ty_args,
                ty_args,
                inferred_ty: _,
            }) => {
                print_mod_prefix(mod_prefix, p);
                p.str(ty);
                print_user_ty_args(ty_user_ty_args, p);
                p.char('.');
                p.str(member);
                print_user_ty_args(user_ty_args, p);
                print_ty_args(ty_args, p);
            }

            Expr::Call(CallExpr {
                fun,
                args,
                splice,
                inferred_ty: _,
            }) => {
                let parens = !matches!(
                    &fun.node,
                    Expr::Var(_)
                        | Expr::FieldSel(_)
                        | Expr::ConSel(_)
                        | Expr::AssocFnSel(_)
                        | Expr::MethodSel(_)
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
                if let Some(splice) = splice {
                    if !args.is_empty() {
                        p.str(", ");
                    }
                    p.str("..");
                    splice.node.print(p);
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

            Expr::Str(parts) => {
                p.char('"');
                for part in parts {
                    match part {
                        StrPart::Str(str) => escape_str_lit(str, p),
                        StrPart::Expr(expr) => {
                            p.char('`');
                            expr.node.print(p);
                            p.char('`');
                        }
                    }
                }
                p.char('"');
            }

            Expr::Char(char) => {
                p.char('\'');
                escape_char_lit(*char, p);
                p.char('\'');
            }

            Expr::BinOp(BinOpExpr { left, right, op }) => {
                let left_parens = expr_parens(&left.node);
                let right_parens = expr_parens(&right.node);
                if left_parens {
                    p.char('(');
                }
                left.node.print(p);
                if left_parens {
                    p.char(')');
                }
                let op_str = match op {
                    BinOp::Add => "+",
                    BinOp::Subtract => "-",
                    BinOp::Equal => "==",
                    BinOp::NotEqual => "!=",
                    BinOp::Multiply => "*",
                    BinOp::Divide => "/",
                    BinOp::Lt => "<",
                    BinOp::Gt => ">",
                    BinOp::LtEq => "<=",
                    BinOp::GtEq => ">=",
                    BinOp::And => "and",
                    BinOp::Or => "or",
                    BinOp::BitOr => "|",
                    BinOp::BitAnd => "&",
                    BinOp::LeftShift => "<<",
                    BinOp::RightShift => ">>",
                };
                p.char(' ');
                p.str(op_str);
                p.char(' ');
                if right_parens {
                    p.char('(');
                }
                right.node.print(p);
                if right_parens {
                    p.char(')');
                }
            }

            Expr::UnOp(UnOpExpr { op, expr }) => {
                match op {
                    UnOp::Not => p.str("not "),
                    UnOp::Neg => p.char('-'),
                }
                let parens = expr_parens(&expr.node);
                if parens {
                    p.char('(');
                }
                expr.node.print(p);
                if parens {
                    p.char(')');
                }
            }

            Expr::Record(RecordExpr {
                fields,
                splice,
                inferred_ty: _,
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

            Expr::Return(ReturnExpr {
                expr,
                inferred_ty: _,
            }) => {
                p.str("return ");
                expr.node.print(p);
            }

            Expr::Match(MatchExpr {
                scrutinee,
                alts,
                inferred_ty: _,
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
                inferred_ty: _,
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

            Expr::Fn(FnExpr {
                sig,
                body,
                inferred_ty,
            }) => {
                p.char('\\');
                sig.print(&None, &Name::new_static(""), p);
                if let Some(inferred_ty) = inferred_ty {
                    write!(p, " #| inferred type = {inferred_ty} |#").unwrap();
                }
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

            Expr::Do(DoExpr {
                stmts,
                inferred_ty: _,
            }) => {
                p.str("do:");
                p.indented(|p| {
                    for stmt in stmts.iter() {
                        p.nl();
                        stmt.node.print(p);
                    }
                });
            }

            Expr::Seq { ty, elems } => {
                if let Some(ty) = ty {
                    p.str(ty);
                    p.char('.');
                }
                p.char('[');
                p.sep(elems.iter(), ", ", |p, (k, v)| {
                    if let Some(k) = k {
                        k.node.print(p);
                        p.str(" = ");
                    }
                    v.node.print(p);
                });
                p.char(']');
            }

            Expr::Variant(VariantExpr {
                expr,
                inferred_ty: _,
            }) => {
                p.char('~');
                expr.node.print(p);
            }
        }
    }
}

impl Pat {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Pat::Var(VarPat { var, ty, refined }) => {
                p.str(var);
                if let Some(ty) = ty {
                    write!(p, ": {ty}").unwrap();
                }
                if let Some(refined) = refined {
                    write!(p, " ~> {refined}").unwrap();
                }
            }

            Pat::Con(ConPat { con, fields, rest }) => {
                con.print(p);

                if !fields.is_empty() || matches!(rest, RestPat::Ignore | RestPat::Bind(_)) {
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

            Pat::Record(RecordPat {
                fields,
                rest,
                inferred_ty,
            }) => {
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
                p.char(')');
                if let Some(ty) = inferred_ty {
                    write!(p, ": {ty}").unwrap();
                }
            }

            Pat::Ignore => p.char('_'),

            Pat::Str(str) => {
                p.char('"');
                escape_str_lit(str, p);
                p.char('"');
            }

            Pat::Char(char) => {
                p.char('\'');
                escape_char_lit(*char, p);
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
                inferred_ty,
                inferred_pat_ty: _,
            }) => {
                p.char('~');
                pat.node.print(p);
                if let Some(ty) = inferred_ty {
                    write!(p, ": {ty}").unwrap();
                }
            }
        }
    }
}

impl Con {
    pub fn print(&self, p: &mut Printer) {
        let Con {
            mod_prefix,
            ty,
            con,
            ty_user_ty_args,
            con_user_ty_args,
            ty_args: _,
            resolved_ty_id: _,
            inferred_ty: _,
        } = self;
        print_mod_prefix(mod_prefix, p);
        p.str(ty);
        print_user_ty_args(ty_user_ty_args, p);
        if let Some(con) = con {
            p.char('.');
            p.str(con);
            print_user_ty_args(con_user_ty_args, p);
        }
        print_ty_args(&self.ty_args, p);
    }
}

impl Kind {
    pub fn print(&self, p: &mut Printer) {
        match self {
            Kind::Star => p.char('*'),
            Kind::Row(RecordOrVariant::Record) => p.str("Row[Rec]"),
            Kind::Row(RecordOrVariant::Variant) => p.str("Row[Var]"),
        }
    }
}

fn print_context(context: &Context, p: &mut Printer) {
    if context.type_params.is_empty() && context.preds.is_empty() {
        return;
    }

    p.char('[');
    p.sep(context.type_params.iter(), ", ", |p, (ty_param, kind)| {
        p.str(ty_param);
        p.str(": ");
        kind.print(p);
    });
    if !context.type_params.is_empty() && !context.preds.is_empty() {
        p.str(", ");
    }
    p.sep(context.preds.iter(), ", ", |p, ty| ty.node.print(p));
    p.char(']');
}

fn print_user_ty_args(args: &[L<Type>], p: &mut Printer) {
    if args.is_empty() {
        return;
    }

    p.char('[');
    p.sep(args.iter(), ", ", |p, ty| ty.node.print(p));
    p.char(']');
}

fn print_mod_prefix(mod_prefix: &Option<crate::module::ModulePath>, p: &mut Printer) {
    if let Some(path) = mod_prefix {
        write!(p, "{path}/").unwrap();
    }
}

fn print_ty_args(args: &[Ty], p: &mut Printer) {
    if args.is_empty() {
        return;
    }

    p.char('[');
    p.sep(args.iter(), ", ", |p, ty| write!(p, "{ty}").unwrap());
    p.char(']');
}

fn expr_parens(expr: &Expr) -> bool {
    !matches!(
        expr,
        Expr::Var(_)
            | Expr::ConSel(_)
            | Expr::FieldSel(_)
            | Expr::MethodSel(_)
            | Expr::AssocFnSel(_)
            | Expr::Call(_)
            | Expr::Int(_)
            | Expr::Str(_)
            | Expr::Char(_)
            | Expr::Record(_)
            | Expr::Seq { .. }
            | Expr::Variant(_)
    )
}

use std::fmt::Display;

impl Display for TopDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

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
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for ImportDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for TraitDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
        f.write_str(p.as_str())
    }
}

impl Display for ImplDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&mut p);
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

impl Display for FunSig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut p = Printer::new();
        self.print(&None, &Name::new(""), &mut p);
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

/// Note: this does not add wrapping single quotes.
pub(crate) fn escape_char_lit(c: char, w: &mut impl Write) {
    match c {
        '\'' => {
            w.write_str("\\'").unwrap();
        }

        '\n' => {
            w.write_str("\\n").unwrap();
        }

        '\t' => {
            w.write_str("\\t").unwrap();
        }

        '\r' => {
            w.write_str("\\r").unwrap();
        }

        '\\' => {
            w.write_str("\\\\").unwrap();
        }

        other => write!(w, "{other}").unwrap(),
    }
}

/// Note: this does not add wrapping double quotes.
pub(crate) fn escape_str_lit(s: &str, w: &mut impl Write) {
    for c in s.chars() {
        match c {
            '"' => {
                w.write_str("\\\"").unwrap();
            }

            '\n' => {
                w.write_str("\\n").unwrap();
            }

            '\t' => {
                w.write_str("\\t").unwrap();
            }

            '\r' => {
                w.write_str("\\r").unwrap();
            }

            '\\' => {
                w.write_str("\\\\").unwrap();
            }

            other => write!(w, "{other}").unwrap(),
        }
    }
}
