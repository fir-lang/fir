use crate::{ast::*, type_checker::RecordOrVariant};

use std::fmt::Write;

pub fn print_module(module: &[L<TopDecl>]) {
    let mut buf = String::new();
    for (i, top_decl) in module.iter().enumerate() {
        if i != 0 {
            println!();
        }
        top_decl.node.print(&mut buf, 0);
        println!("{buf}");
        buf.clear();
    }
}

impl TopDecl {
    pub fn print(&self, buf: &mut String, indent: u32) {
        match self {
            TopDecl::Type(decl) => decl.node.print(buf, indent),
            TopDecl::Fun(decl) => decl.node.print(buf, indent),
            TopDecl::Import(decl) => decl.node.print(buf),
            TopDecl::Trait(decl) => decl.node.print(buf, indent),
            TopDecl::Impl(decl) => decl.node.print(buf, indent),
        }
    }
}

impl TypeDecl {
    pub fn print(&self, buf: &mut String, indent: u32) {
        buf.push_str("type ");
        buf.push_str(&self.name);

        if !self.type_params.is_empty() {
            buf.push('[');
            for (i, type_param) in self.type_params.iter().enumerate() {
                if i != 0 {
                    buf.push_str(", ");
                }
                buf.push_str(type_param);
            }
            buf.push(']');
        }

        if let Some(rhs) = &self.rhs {
            rhs.print(buf, indent + 4);
        }
    }
}

impl TypeDeclRhs {
    pub fn print(&self, buf: &mut String, indent: u32) {
        match self {
            TypeDeclRhs::Sum(cons) => {
                buf.push_str(":\n");
                for (i, con) in cons.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[..indent as usize]);
                    buf.push_str(&con.name);
                    match &con.fields {
                        ConFields::Empty => {}

                        ConFields::Named(fields) => {
                            buf.push_str("(\n");
                            for (field_name, field_ty) in fields.iter() {
                                buf.push_str(&INDENTS[..indent as usize + 4]);
                                buf.push_str(field_name);
                                buf.push_str(": ");
                                field_ty.node.print(buf);
                                buf.push_str(",\n");
                            }
                            buf.push_str("    )");
                        }

                        ConFields::Unnamed(fields) => {
                            buf.push('(');
                            for (i, field_ty) in fields.iter().enumerate() {
                                if i != 0 {
                                    buf.push_str(", ");
                                }
                                field_ty.node.print(buf);
                            }
                            buf.push(')');
                        }
                    }
                }
            }

            TypeDeclRhs::Product(fields) => match fields {
                ConFields::Empty => {}

                ConFields::Named(fields) => {
                    buf.push_str("(\n");
                    for (field_name, field_ty) in fields.iter() {
                        buf.push_str(&INDENTS[..indent as usize]);
                        buf.push_str(field_name);
                        buf.push_str(": ");
                        field_ty.node.print(buf);
                        buf.push_str(",\n");
                    }
                    buf.push(')');
                }

                ConFields::Unnamed(fields) => {
                    buf.push('(');
                    for (i, field_ty) in fields.iter().enumerate() {
                        if i != 0 {
                            buf.push_str(", ");
                        }
                        field_ty.node.print(buf);
                    }
                    buf.push(')');
                }
            },
        }
    }
}

impl FunDecl {
    pub fn print(&self, buf: &mut String, indent: u32) {
        self.sig.print(&self.parent_ty, &self.name.node, buf);
        if let Some(body) = &self.body {
            buf.push_str(":\n");
            for (i, stmt) in body.iter().enumerate() {
                if i != 0 {
                    buf.push('\n');
                }
                buf.push_str(&INDENTS[..indent as usize + 4]);
                stmt.node.print(buf, indent + 4);
            }
        }
    }
}

impl ImportDecl {
    pub fn print(&self, buf: &mut String) {
        buf.push_str("import [\n");
        for path in self.paths.iter() {
            let parts: Vec<&str> = path.iter().map(|s| s.as_str()).collect();
            buf.push_str(&parts.join("/"));
            buf.push_str(",\n");
        }
    }
}

impl TraitDecl {
    pub fn print(&self, buf: &mut String, indent: u32) {
        buf.push_str(&INDENTS[..indent as usize]);
        buf.push_str("trait ");
        buf.push_str(&self.name.node);
        buf.push('[');
        for (i, ty) in self.type_params.iter().enumerate() {
            if i != 0 {
                buf.push_str(", ");
            }
            buf.push_str(&ty.node);
        }
        buf.push_str("]:\n");
        for (i, item) in self.items.iter().enumerate() {
            if i != 0 {
                buf.push('\n');
            }
            buf.push_str(&INDENTS[..indent as usize + 4]);
            item.node.print(buf, indent + 4);
        }
    }
}

impl ImplDecl {
    pub fn print(&self, buf: &mut String, indent: u32) {
        buf.push_str("impl");
        print_context(&self.context, buf);
        buf.push(' ');
        buf.push_str(&self.trait_.node);
        buf.push('[');
        for (i, ty) in self.tys.iter().enumerate() {
            if i != 0 {
                buf.push_str(", ")
            }
            ty.node.print(buf);
        }
        buf.push_str("]:\n");
        for (i, item) in self.items.iter().enumerate() {
            if i != 0 {
                buf.push('\n');
                buf.push('\n');
            }
            buf.push_str(&INDENTS[..indent as usize + 4]);
            item.node.print(buf, indent + 4);
        }
    }
}

impl Type {
    pub fn print(&self, buf: &mut String) {
        match self {
            Type::Named(ty) => {
                ty.print(buf);
            }

            Type::Var(var) => buf.push_str(var),

            Type::Record {
                fields,
                extension,
                is_row,
            } => {
                if *is_row {
                    buf.push_str("row(");
                } else {
                    buf.push('(');
                }
                for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(field_name);
                    buf.push_str(": ");
                    field_ty.print(buf);
                }
                if let Some(extension) = extension {
                    buf.push('|');
                    buf.push_str(extension);
                }
                buf.push(')');
            }

            Type::Variant {
                alts,
                extension,
                is_row,
            } => {
                if *is_row {
                    buf.push_str("row[");
                } else {
                    buf.push('[');
                }
                for (i, NamedType { name, args }) in alts.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(name);
                    if !args.is_empty() {
                        buf.push('(');
                        for (i, L { loc: _, node }) in args.iter().enumerate() {
                            if i != 0 {
                                buf.push_str(", ");
                            }
                            buf.push_str(name);
                            buf.push_str(": ");
                            node.print(buf);
                        }
                        buf.push(')');
                    }
                }
                if let Some(ext) = extension {
                    if !alts.is_empty() {
                        buf.push_str(", ");
                    }
                    buf.push_str("..");
                    buf.push_str(ext);
                }
                buf.push(']');
            }

            Type::Fn(FnType {
                args,
                ret,
                exceptions,
            }) => {
                buf.push_str("Fn(");
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    arg.node.print(buf);
                }
                buf.push(')');
                if let Some(ret) = ret {
                    buf.push(' ');
                    ret.node.print(buf);
                }
                if let Some(exn) = exceptions {
                    buf.push_str(" / ");
                    exn.node.print(buf);
                }
            }
        }
    }
}

impl NamedType {
    pub fn print(&self, buf: &mut String) {
        buf.push_str(&self.name);
        if !self.args.is_empty() {
            buf.push('[');
            for (i, arg) in self.args.iter().enumerate() {
                if i != 0 {
                    buf.push_str(", ");
                }
                arg.node.print(buf);
            }
            buf.push(']');
        }
    }
}

impl FunSig {
    pub fn print(&self, parent_ty: &Option<L<Id>>, name: &Id, buf: &mut String) {
        if let Some(parent_ty) = parent_ty {
            buf.push_str(&parent_ty.node);
            buf.push('.');
        }
        buf.push_str(name);
        print_context(&self.context, buf);
        buf.push('(');
        match &self.self_ {
            SelfParam::No => {}
            SelfParam::Implicit => {
                buf.push_str("self");
                if !self.params.is_empty() {
                    buf.push_str(", ");
                }
            }
            SelfParam::Explicit(ty) => {
                buf.push_str("self: ");
                ty.node.print(buf);
                if !self.params.is_empty() {
                    buf.push_str(", ");
                }
            }
        }
        for (i, (param_name, param_ty)) in self.params.iter().enumerate() {
            if i != 0 {
                buf.push_str(", ");
            }
            buf.push_str(param_name);
            if let Some(param_ty) = param_ty {
                buf.push_str(": ");
                param_ty.node.print(buf);
            }
        }
        buf.push(')');
        if let Some(ret_ty) = &self.return_ty {
            buf.push(' ');
            ret_ty.node.print(buf);
        }
        if let Some(exn) = &self.exceptions {
            buf.push_str(" / ");
            exn.node.print(buf);
        }
    }
}

impl Stmt {
    pub fn print(&self, buf: &mut String, indent: u32) {
        match self {
            Stmt::Break { label, level: _ } => {
                buf.push_str("break");
                if let Some(label) = label {
                    buf.push_str(" \'");
                    buf.push_str(label);
                }
            }

            Stmt::Continue { label, level: _ } => {
                buf.push_str("continue");
                if let Some(label) = label {
                    buf.push_str(" \'");
                    buf.push_str(label);
                }
            }

            Stmt::Let(LetStmt { lhs, ty, rhs }) => {
                buf.push_str("let ");
                lhs.node.print(buf);
                if let Some(ty) = ty {
                    buf.push_str(": ");
                    ty.node.print(buf);
                }
                buf.push_str(" = ");
                rhs.node.print(buf, indent);
            }

            Stmt::Assign(AssignStmt { lhs, rhs, op }) => {
                lhs.node.print(buf, indent);
                let op_str = match op {
                    AssignOp::Eq => "=",
                    AssignOp::PlusEq => "+=",
                    AssignOp::MinusEq => "-=",
                    AssignOp::StarEq => "*=",
                    AssignOp::CaretEq => "^=",
                };
                buf.push(' ');
                buf.push_str(op_str);
                buf.push(' ');
                rhs.node.print(buf, indent);
            }

            Stmt::Expr(expr) => expr.print(buf, indent),

            Stmt::For(ForStmt {
                label,
                pat,
                item_ast_ty,
                item_tc_ty: _,
                expr,
                expr_ty: _,
                body,
            }) => {
                if let Some(label) = label {
                    buf.push('\'');
                    buf.push_str(label);
                    buf.push_str(": ");
                }
                buf.push_str("for ");
                pat.node.print(buf);
                if let Some(ty) = item_ast_ty {
                    buf.push_str(": ");
                    ty.node.print(buf);
                }
                buf.push_str(" in ");
                expr.node.print(buf, indent);
                buf.push_str(":\n");
                for (i, stmt) in body.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[..indent as usize + 4]);
                    stmt.node.print(buf, indent + 4);
                }
            }

            Stmt::While(WhileStmt { label, cond, body }) => {
                if let Some(label) = label {
                    buf.push('\'');
                    buf.push_str(label);
                    buf.push_str(": ");
                }
                buf.push_str("while ");
                cond.node.print(buf, indent);
                buf.push_str(":\n");
                for (i, stmt) in body.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[..indent as usize + 4]);
                    stmt.node.print(buf, indent + 4);
                }
            }
        }
    }
}

impl Expr {
    pub fn print(&self, buf: &mut String, indent: u32) {
        match self {
            Expr::Var(VarExpr {
                id,
                user_ty_args,
                ty_args,
                inferred_ty: _,
            }) => {
                buf.push_str(id);
                print_user_ty_args(user_ty_args, buf);
                print_ty_args(ty_args, buf);
            }

            Expr::FieldSel(FieldSelExpr {
                object,
                field,
                user_ty_args,
                inferred_ty: _,
            }) => {
                object.node.print(buf, indent);
                buf.push('.');
                buf.push_str(field);
                print_user_ty_args(user_ty_args, buf);
            }

            Expr::MethodSel(MethodSelExpr {
                object,
                object_ty: _,
                method_ty_id,
                method,
                ty_args,
                inferred_ty: _,
            }) => {
                object.node.print(buf, indent);
                buf.push_str(".{");
                buf.push_str(method_ty_id);
                buf.push_str(".}");
                buf.push_str(method);
                print_ty_args(ty_args, buf);
            }

            Expr::ConSel(con) => {
                con.print(buf);
            }

            Expr::AssocFnSel(AssocFnSelExpr {
                ty,
                ty_user_ty_args,
                member,
                user_ty_args,
                ty_args,
                inferred_ty: _,
            }) => {
                buf.push_str(ty);
                print_user_ty_args(ty_user_ty_args, buf);
                buf.push('.');
                buf.push_str(member);
                print_user_ty_args(user_ty_args, buf);
                print_ty_args(ty_args, buf);
            }

            Expr::Call(CallExpr {
                fun,
                args,
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
                    buf.push('(');
                }
                fun.node.print(buf, indent);
                if parens {
                    buf.push(')');
                }
                buf.push('(');
                for (i, CallArg { name, expr }) in args.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    if let Some(name) = name {
                        buf.push_str(name);
                        buf.push_str(" = ");
                    }
                    expr.node.print(buf, indent);
                }
                buf.push(')');
            }

            Expr::Int(IntExpr {
                text,
                kind,
                parsed: _,
            }) => {
                buf.push_str(text);
                match kind {
                    Some(IntKind::I64(_)) => buf.push_str("I64"),
                    Some(IntKind::U64(_)) => buf.push_str("U64"),
                    Some(IntKind::I32(_)) => buf.push_str("I32"),
                    Some(IntKind::U32(_)) => buf.push_str("U32"),
                    Some(IntKind::I8(_)) => buf.push_str("I8"),
                    Some(IntKind::U8(_)) => buf.push_str("U8"),
                    None => {}
                }
            }

            Expr::Str(parts) => {
                buf.push('"');
                for part in parts {
                    match part {
                        StrPart::Str(str) => escape_str_lit(str, buf),
                        StrPart::Expr(expr) => {
                            buf.push('`');
                            expr.node.print(buf, indent);
                            buf.push('`');
                        }
                    }
                }
                buf.push('"');
            }

            Expr::Char(char) => {
                buf.push('\'');
                escape_char_lit(*char, buf);
                buf.push('\'');
            }

            Expr::BinOp(BinOpExpr { left, right, op }) => {
                let left_parens = expr_parens(&left.node);
                let right_parens = expr_parens(&right.node);
                if left_parens {
                    buf.push('(');
                }
                left.node.print(buf, indent);
                if left_parens {
                    buf.push(')');
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
                    BinOp::And => "&&",
                    BinOp::Or => "||",
                    BinOp::BitOr => "|",
                    BinOp::BitAnd => "&",
                    BinOp::LeftShift => "<<",
                    BinOp::RightShift => ">>",
                };
                buf.push(' ');
                buf.push_str(op_str);
                buf.push(' ');
                if right_parens {
                    buf.push('(');
                }
                right.node.print(buf, indent);
                if right_parens {
                    buf.push(')');
                }
            }

            Expr::UnOp(UnOpExpr { op, expr }) => {
                match op {
                    UnOp::Not => buf.push_str("not "),
                    UnOp::Neg => buf.push('-'),
                }
                let parens = expr_parens(&expr.node);
                if parens {
                    buf.push('(');
                }
                expr.node.print(buf, indent);
                if parens {
                    buf.push(')');
                }
            }

            Expr::Record(RecordExpr {
                fields,
                inferred_ty: _,
            }) => {
                buf.push('(');
                for (i, (field_name, field_expr)) in fields.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(field_name);
                    buf.push_str(" = ");
                    field_expr.node.print(buf, 0);
                }
                buf.push(')');
            }

            Expr::Return(ReturnExpr {
                expr,
                inferred_ty: _,
            }) => {
                buf.push_str("return ");
                expr.node.print(buf, 0);
            }

            Expr::Match(MatchExpr {
                scrutinee,
                alts,
                inferred_ty: _,
            }) => {
                buf.push_str("match ");
                scrutinee.node.print(buf, indent);
                buf.push_str(":\n");
                for (i, Alt { pat, guard, rhs }) in alts.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[..indent as usize + 4]);
                    pat.node.print(buf);
                    if let Some(guard) = guard {
                        buf.push_str(" if ");
                        guard.node.print(buf, indent + 8);
                    }
                    buf.push_str(":\n");
                    for (j, stmt) in rhs.iter().enumerate() {
                        if j != 0 {
                            buf.push('\n');
                        }
                        buf.push_str(&INDENTS[..indent as usize + 8]);
                        stmt.node.print(buf, indent + 8);
                    }
                }
            }

            Expr::If(IfExpr {
                branches,
                else_branch,
                inferred_ty: _,
            }) => {
                buf.push_str("if ");
                branches[0].0.node.print(buf, indent);
                buf.push_str(":\n");
                for (i, stmt) in branches[0].1.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[..indent as usize + 4]);
                    stmt.node.print(buf, indent + 4);
                }
                for branch in &branches[1..] {
                    buf.push('\n');
                    buf.push_str(&INDENTS[..indent as usize]);
                    buf.push_str("elif ");
                    branch.0.node.print(buf, indent);
                    buf.push_str(":\n");
                    for (i, stmt) in branch.1.iter().enumerate() {
                        if i != 0 {
                            buf.push('\n');
                        }
                        buf.push_str(&INDENTS[..indent as usize + 4]);
                        stmt.node.print(buf, indent + 4);
                    }
                }
                if let Some(else_branch) = else_branch {
                    buf.push('\n');
                    buf.push_str(&INDENTS[..indent as usize]);
                    buf.push_str("else:\n");
                    for (i, stmt) in else_branch.iter().enumerate() {
                        if i != 0 {
                            buf.push('\n');
                        }
                        buf.push_str(&INDENTS[..indent as usize + 4]);
                        stmt.node.print(buf, indent + 4);
                    }
                }
            }

            Expr::Fn(FnExpr {
                sig,
                body,
                inferred_ty,
            }) => {
                buf.push('\\');
                sig.print(&None, &SmolStr::new_static(""), buf);
                if let Some(inferred_ty) = inferred_ty {
                    write!(buf, " #| inferred type = {inferred_ty} |#").unwrap();
                }
                buf.push_str(" {\n");
                for stmt in body.iter() {
                    buf.push_str(&INDENTS[..indent as usize + 4]);
                    stmt.node.print(buf, indent + 4);
                    buf.push('\n');
                }
                buf.push_str(&INDENTS[..indent as usize]);
                buf.push('}');
            }

            Expr::Is(IsExpr { expr, pat }) => {
                buf.push('(');
                expr.node.print(buf, indent);
                buf.push_str(" is ");
                pat.node.print(buf);
                buf.push(')');
            }

            Expr::Do(DoExpr {
                stmts,
                inferred_ty: _,
            }) => {
                buf.push_str("do:\n");
                for (i, stmt) in stmts.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[..indent as usize + 4]);
                    stmt.node.print(buf, indent + 4);
                }
            }

            Expr::Seq { ty, elems } => {
                if let Some(ty) = ty {
                    buf.push_str(ty);
                    buf.push('.');
                }
                buf.push('[');
                for (i, (k, v)) in elems.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    if let Some(k) = k {
                        k.node.print(buf, indent + 4);
                        buf.push_str(" = ");
                    }
                    v.node.print(buf, indent + 4);
                }
                buf.push(']');
            }

            Expr::Variant(VariantExpr {
                expr,
                inferred_ty: _,
            }) => {
                buf.push('~');
                expr.node.print(buf, indent);
            }
        }
    }
}

impl Pat {
    pub fn print(&self, buf: &mut String) {
        match self {
            Pat::Var(VarPat { var, ty }) => {
                buf.push_str(var);
                if let Some(ty) = ty {
                    write!(buf, ": {ty}").unwrap();
                }
            }

            Pat::Con(ConPat {
                con,
                fields,
                ignore_rest,
            }) => {
                con.print(buf);

                if !fields.is_empty() || *ignore_rest {
                    buf.push('(');
                    for (i, field) in fields.iter().enumerate() {
                        if i != 0 {
                            buf.push_str(", ");
                        }
                        if let Some(name) = &field.name {
                            buf.push_str(name);
                            buf.push_str(" = ");
                        }
                        field.node.node.print(buf);
                    }
                    if *ignore_rest {
                        if !fields.is_empty() {
                            buf.push_str(", ");
                        }
                        buf.push_str("..");
                    }
                    buf.push(')');
                }
            }

            Pat::Record(RecordPat {
                fields,
                ignore_rest,
                inferred_ty,
            }) => {
                buf.push('(');
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    let Named { name, node } = field;
                    if let Some(name) = name {
                        buf.push_str(name);
                        buf.push_str(" = ");
                    }
                    node.node.print(buf);
                }
                if *ignore_rest {
                    if !fields.is_empty() {
                        buf.push_str(", ");
                    }
                    buf.push_str("..");
                }
                buf.push(')');
                if let Some(ty) = inferred_ty {
                    write!(buf, ": {ty}").unwrap();
                }
            }

            Pat::Ignore => buf.push('_'),

            Pat::Str(str) => {
                buf.push('"');
                escape_str_lit(str, buf);
                buf.push('"');
            }

            Pat::Char(char) => {
                buf.push('\'');
                escape_char_lit(*char, buf);
                buf.push('\'');
            }

            Pat::Or(pat1, pat2) => {
                buf.push('(');
                pat1.node.print(buf);
                buf.push_str(") | (");
                pat2.node.print(buf);
                buf.push(')');
            }

            Pat::Variant(VariantPat { pat, inferred_ty }) => {
                buf.push('~');
                pat.node.print(buf);
                if let Some(ty) = inferred_ty {
                    write!(buf, ": {ty}").unwrap();
                }
            }
        }
    }
}

impl Con {
    pub fn print(&self, buf: &mut String) {
        buf.push_str(&self.ty);
        if let Some(con) = &self.con {
            buf.push('.');
            buf.push_str(con);
        }
        print_ty_args(&self.ty_args, buf);
    }
}

fn print_context(context: &Context, buf: &mut String) {
    if context.type_params.is_empty() && context.preds.is_empty() {
        return;
    }

    buf.push('[');

    for (i, (ty_param, kind)) in context.type_params.iter().enumerate() {
        if i != 0 {
            buf.push_str(", ");
        }
        buf.push_str(ty_param);
        buf.push_str(": ");
        let kind_str = match kind {
            Kind::Star => "*",
            Kind::Row(RecordOrVariant::Record) => "row(rec)",
            Kind::Row(RecordOrVariant::Variant) => "row(var)",
        };
        buf.push_str(kind_str);
    }

    for (i, ty) in context.preds.iter().enumerate() {
        if !context.type_params.is_empty() || i != 0 {
            buf.push_str(", ");
        }
        ty.node.print(buf);
    }

    buf.push(']');
}

fn print_user_ty_args(args: &[L<Type>], buf: &mut String) {
    if args.is_empty() {
        return;
    }

    buf.push('[');
    for (i, ty) in args.iter().enumerate() {
        if i != 0 {
            buf.push_str(", ");
        }
        ty.node.print(buf);
    }
    buf.push(']');
}

fn print_ty_args(args: &[Ty], buf: &mut String) {
    if args.is_empty() {
        return;
    }

    buf.push('[');
    for (i, ty) in args.iter().enumerate() {
        if i != 0 {
            buf.push_str(", ");
        }
        buf.push_str(&ty.to_string());
    }
    buf.push(']');
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

const INDENTS: &str = "                                                  ";

use std::fmt::Display;

impl Display for TopDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for TypeDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for TypeDeclRhs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for FunDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for ImportDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s);
        f.write_str(&s)
    }
}

impl Display for TraitDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for ImplDecl {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s);
        f.write_str(&s)
    }
}

impl Display for FunSig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&None, &SmolStr::new(""), &mut s);
        f.write_str(&s)
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s, 0);
        f.write_str(&s)
    }
}

impl Display for Pat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s);
        f.write_str(&s)
    }
}

/// Note: this does not add wrapping single quotes.
pub(crate) fn escape_char_lit(c: char, buf: &mut String) {
    match c {
        '\'' => {
            buf.push_str("\\'");
        }

        '\n' => {
            buf.push_str("\\n");
        }

        '\t' => {
            buf.push_str("\\t");
        }

        '\r' => {
            buf.push_str("\\r");
        }

        '\\' => {
            buf.push_str("\\\\");
        }

        other => buf.push(other),
    }
}

/// Note: this does not add wrapping double quotes.
pub(crate) fn escape_str_lit(s: &str, buf: &mut String) {
    for c in s.chars() {
        match c {
            '"' => {
                buf.push_str("\\\"");
            }

            '\n' => {
                buf.push_str("\\n");
            }

            '\t' => {
                buf.push_str("\\t");
            }

            '\r' => {
                buf.push_str("\\r");
            }

            '\\' => {
                buf.push_str("\\\\");
            }

            other => buf.push(other),
        }
    }
}
