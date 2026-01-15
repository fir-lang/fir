use crate::mono_ast::*;

use smol_str::SmolStr;

pub fn print_pgm(pgm: &MonoPgm) {
    let mut s = String::new();
    pgm.print(&mut s);
    println!("{s}");
}

impl MonoPgm {
    pub fn print(&self, buf: &mut String) {
        for ty_arg_map in self.ty.values() {
            for (ty_args, ty_decl) in ty_arg_map.iter() {
                buf.push_str("type ");
                buf.push_str(&ty_decl.name);
                print_ty_args(ty_args, buf);
                if let Some(rhs) = &ty_decl.rhs {
                    rhs.print(buf, 4);
                }
                buf.push('\n');
                buf.push('\n');
            }
        }

        for fun_insts in self.funs.values() {
            for (ty_args, fun) in fun_insts.iter() {
                fun.print(buf, ty_args, 0);
                buf.push('\n');
                buf.push('\n');
            }
        }

        for ty_arg_map in self
            .associated
            .values()
            .flat_map(|method_map| method_map.values())
        {
            for (ty_args, fun) in ty_arg_map.iter() {
                fun.print(buf, ty_args, 0);
                buf.push('\n');
                buf.push('\n');
            }
        }
    }
}

impl TypeDecl {
    pub fn print(&self, buf: &mut String, indent: u32) {
        buf.push_str("type ");
        buf.push_str(&self.name);

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
                                field_ty.print(buf);
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
                                field_ty.print(buf);
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
                        field_ty.print(buf);
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
                        field_ty.print(buf);
                    }
                    buf.push(')');
                }
            },
        }
    }
}

impl FunDecl {
    pub fn print(&self, buf: &mut String, ty_args: &[Type], indent: u32) {
        self.sig
            .print(&self.parent_ty, &self.name.node, ty_args, buf);
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

impl Type {
    pub fn print(&self, buf: &mut String) {
        match self {
            Type::Named(ty) => {
                ty.print(buf);
            }

            Type::Record { fields } => {
                buf.push('(');
                for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(field_name);
                    buf.push_str(": ");
                    field_ty.print(buf);
                }
                buf.push(')');
            }

            Type::Variant { alts } => {
                buf.push('[');
                for (i, ty) in alts.values().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    ty.print(buf);
                }
                buf.push(']');
            }

            Type::Fn(FnType { args, ret, exn }) => {
                buf.push_str("Fn(");
                match args {
                    FunArgs::Positional(args) => {
                        for (i, arg) in args.iter().enumerate() {
                            if i != 0 {
                                buf.push_str(", ");
                            }
                            arg.print(buf);
                        }
                    }
                    FunArgs::Named(args) => {
                        for (i, (name, ty)) in args.iter().enumerate() {
                            if i != 0 {
                                buf.push_str(", ");
                            }
                            buf.push_str(name);
                            buf.push_str(": ");
                            ty.print(buf);
                        }
                    }
                }
                buf.push(')');
                buf.push(' ');
                ret.print(buf);
                buf.push_str(" / ");
                exn.print(buf);
            }

            Type::Never => {
                buf.push('!');
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
                arg.print(buf);
            }
            buf.push(']');
        }
    }
}

impl FunSig {
    pub fn print(&self, parent_ty: &Option<L<Id>>, name: &Id, ty_args: &[Type], buf: &mut String) {
        if let Some(parent_ty) = parent_ty {
            buf.push_str(&parent_ty.node);
            buf.push('.');
        }
        buf.push_str(name);
        print_ty_args(ty_args, buf);
        buf.push('(');
        for (i, (param_name, param_ty)) in self.params.iter().enumerate() {
            if i != 0 {
                buf.push_str(", ");
            }
            buf.push_str(param_name);
            buf.push_str(": ");
            param_ty.node.print(buf);
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

            Stmt::Let(LetStmt { lhs, rhs }) => {
                buf.push_str("let ");
                lhs.node.print(buf);
                buf.push_str(" = ");
                rhs.node.print(buf, indent);
            }

            Stmt::Assign(AssignStmt { lhs, rhs }) => {
                lhs.node.print(buf, 0);
                buf.push_str(" = ");
                rhs.node.print(buf, 0);
            }

            Stmt::Expr(expr) => expr.node.print(buf, indent),

            Stmt::While(WhileStmt { label, cond, body }) => {
                if let Some(label) = label {
                    buf.push('\'');
                    buf.push_str(label);
                    buf.push_str(": ");
                }
                buf.push_str("while ");
                cond.node.print(buf, 0);
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
            Expr::LocalVar(id) => {
                buf.push_str(id);
            }

            Expr::TopVar(VarExpr { id, ty_args }) => {
                buf.push_str(id);
                print_ty_args(ty_args, buf);
            }

            Expr::FieldSel(FieldSelExpr { object, field }) => {
                object.node.print(buf, 0);
                buf.push('.');
                buf.push_str(field);
            }

            Expr::ConSel(con) => {
                con.print(buf);
            }

            Expr::AssocFnSel(AssocFnSelExpr {
                ty,
                member,
                ty_args,
            }) => {
                buf.push_str(ty);
                buf.push('.');
                buf.push_str(member);
                print_ty_args(ty_args, buf);
            }

            Expr::Call(CallExpr { fun, args }) => {
                let parens = !matches!(
                    &fun.node,
                    Expr::LocalVar(_)
                        | Expr::TopVar(_)
                        | Expr::FieldSel(_)
                        | Expr::ConSel(_)
                        | Expr::AssocFnSel(_)
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

            Expr::Str(str) => {
                buf.push('"');
                crate::ast::printer::escape_str_lit(str, buf);
                buf.push('"');
            }

            Expr::Char(char) => {
                buf.push('\'');
                crate::ast::printer::escape_char_lit(*char, buf);
                buf.push('\'');
            }

            Expr::BinOp(BinOpExpr { left, right, op }) => {
                let left_parens = expr_parens(&left.node);
                let right_parens = expr_parens(&left.node);
                if left_parens {
                    buf.push('(');
                }
                left.node.print(buf, 0);
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
                right.node.print(buf, 0);
                if right_parens {
                    buf.push(')');
                }
            }

            Expr::Return(expr) => {
                buf.push_str("return ");
                expr.node.print(buf, 0);
            }

            Expr::Match(MatchExpr { scrutinee, alts }) => {
                buf.push_str("match ");
                scrutinee.node.print(buf, 0);
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
            }) => {
                buf.push_str("if ");
                branches[0].0.node.print(buf, 0);
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

            Expr::Fn(FnExpr { sig, body }) => {
                buf.push('\\');
                sig.print(&None, &SmolStr::new_static(""), &[], buf);
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

            Expr::Do(body) => {
                buf.push_str("do:\n");
                for (i, stmt) in body.iter().enumerate() {
                    if i != 0 {
                        buf.push('\n');
                    }
                    buf.push_str(&INDENTS[..indent as usize + 4]);
                    stmt.node.print(buf, indent + 4);
                }
            }

            Expr::Record(RecordExpr { fields, ty: _ }) => {
                buf.push('(');
                for (i, (field_name, field_expr)) in fields.iter().enumerate() {
                    if i != 0 {
                        buf.push_str(", ");
                    }
                    buf.push_str(field_name);
                    buf.push_str(" = ");
                    field_expr.node.print(buf, indent);
                }
                buf.push(')');
            }

            Expr::Variant(VariantExpr { expr, ty: _ }) => {
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
                buf.push_str(": ");
                ty.print(buf);
            }

            Pat::Con(ConPat { con, fields }) => {
                con.print(buf);

                if !fields.is_empty() {
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
                    buf.push(')');
                }
            }

            Pat::Record(RecordPat { fields, ty }) => {
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
                buf.push_str("): ");
                Type::Record { fields: ty.clone() }.print(buf);
            }

            Pat::Ignore => buf.push('_'),

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

            Pat::Or(pat1, pat2) => {
                buf.push('(');
                pat1.node.print(buf);
                buf.push_str(") | (");
                pat2.node.print(buf);
                buf.push(')');
            }

            Pat::Variant(VariantPat { pat, ty: _ }) => {
                buf.push('~');
                pat.node.print(buf);
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

fn expr_parens(expr: &Expr) -> bool {
    !matches!(
        expr,
        Expr::LocalVar(_) | Expr::TopVar(_) | Expr::FieldSel(_) | Expr::ConSel(_)
    )
}

fn print_ty_args(args: &[Type], buf: &mut String) {
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

const INDENTS: &str = "                                                                                               ";

use std::fmt::Display;

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
        self.print(&mut s, &[], 0);
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

impl Display for NamedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&mut s);
        f.write_str(&s)
    }
}

impl Display for FunSig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = String::new();
        self.print(&None, &SmolStr::new(""), &[], &mut s);
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
