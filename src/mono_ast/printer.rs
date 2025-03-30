use crate::mono_ast::*;

use smol_str::SmolStr;

pub fn print_pgm(pgm: &MonoPgm) {
    let mut s = String::new();
    pgm.print(&mut s);
    println!("{}", s);
}

impl MonoPgm {
    pub fn print(&self, buffer: &mut String) {
        for (_, ty_arg_map) in &self.ty {
            for (ty_args, ty_decl) in ty_arg_map.iter() {
                buffer.push_str("type ");
                buffer.push_str(&ty_decl.name);
                print_ty_args(ty_args, buffer);
                if let Some(rhs) = &ty_decl.rhs {
                    rhs.print(buffer, 4);
                }
                buffer.push('\n');
                buffer.push('\n');
            }
        }

        for fun_insts in self.funs.values() {
            for (ty_args, fun) in fun_insts.iter() {
                fun.print(buffer, ty_args, 0);
                buffer.push('\n');
                buffer.push('\n');
            }
        }

        for ty_arg_map in self
            .associated
            .values()
            .flat_map(|method_map| method_map.values())
        {
            for (ty_args, fun) in ty_arg_map.iter() {
                fun.print(buffer, ty_args, 0);
                buffer.push('\n');
                buffer.push('\n');
            }
        }
    }
}

impl TypeDecl {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        buffer.push_str("type ");
        buffer.push_str(&self.name);

        if let Some(rhs) = &self.rhs {
            rhs.print(buffer, indent + 4);
        }
    }
}

impl TypeDeclRhs {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            TypeDeclRhs::Sum(constrs) => {
                buffer.push_str(":\n");
                for (i, constr) in constrs.iter().enumerate() {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..indent as usize]);
                    buffer.push_str(&constr.name);
                    match &constr.fields {
                        ConstructorFields::Empty => {}

                        ConstructorFields::Named(fields) => {
                            buffer.push_str(":\n");
                            for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                                if i != 0 {
                                    buffer.push('\n');
                                }
                                buffer.push_str(&INDENTS[0..indent as usize]);
                                buffer.push_str(field_name);
                                buffer.push_str(": ");
                                field_ty.print(buffer);
                            }
                        }

                        ConstructorFields::Unnamed(fields) => {
                            buffer.push('(');
                            for (i, field_ty) in fields.iter().enumerate() {
                                if i != 0 {
                                    buffer.push_str(", ");
                                }
                                field_ty.print(buffer);
                            }
                            buffer.push(')');
                        }
                    }
                }
            }

            TypeDeclRhs::Product(fields) => match fields {
                ConstructorFields::Empty => {}

                ConstructorFields::Named(fields) => {
                    buffer.push_str(":\n");
                    for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                        if i != 0 {
                            buffer.push('\n');
                        }
                        buffer.push_str(&INDENTS[0..indent as usize]);
                        buffer.push_str(field_name);
                        buffer.push_str(": ");
                        field_ty.print(buffer);
                    }
                }

                ConstructorFields::Unnamed(fields) => {
                    buffer.push('(');
                    for (i, field_ty) in fields.iter().enumerate() {
                        if i != 0 {
                            buffer.push_str(", ");
                        }
                        field_ty.print(buffer);
                    }
                    buffer.push(')');
                }
            },
        }
    }
}

impl FunDecl {
    pub fn print(&self, buffer: &mut String, ty_args: &[Type], indent: u32) {
        self.sig
            .print(&self.parent_ty, &self.name.node, ty_args, buffer);
        if let Some(body) = &self.body {
            buffer.push('\n');
            for (i, stmt) in body.iter().enumerate() {
                if i != 0 {
                    buffer.push('\n');
                }
                buffer.push_str(&INDENTS[0..indent as usize + 4]);
                stmt.node.print(buffer, indent + 4);
            }
        }
    }
}

impl Type {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Type::Named(NamedType { name, args }) => {
                buffer.push_str(name);
                if !args.is_empty() {
                    buffer.push('[');
                    for (i, arg) in args.iter().enumerate() {
                        if i != 0 {
                            buffer.push_str(", ");
                        }
                        arg.node.print(buffer);
                    }
                    buffer.push(']');
                }
            }

            Type::Record { fields } => {
                buffer.push('(');
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = &field.name {
                        buffer.push_str(name);
                        buffer.push_str(": ");
                    }
                    field.node.print(buffer);
                }
                buffer.push(')');
            }

            Type::Variant { alts } => {
                buffer.push('[');
                for (i, VariantAlt { con, fields }) in alts.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    buffer.push_str(con);
                    if !fields.is_empty() {
                        buffer.push('(');
                        for (i, Named { name, node }) in fields.iter().enumerate() {
                            if i != 0 {
                                buffer.push_str(", ");
                            }
                            if let Some(name) = name {
                                buffer.push_str(name);
                                buffer.push_str(": ");
                            }
                            node.print(buffer);
                        }
                        buffer.push(')');
                    }
                }
                buffer.push(']');
            }

            Type::Fn(FnType {
                args,
                ret,
                exceptions,
            }) => {
                buffer.push_str("Fn(");
                match args {
                    FunArgs::Positional(args) => {
                        for (i, arg) in args.iter().enumerate() {
                            if i > 0 {
                                buffer.push_str(", ");
                            }
                            arg.print(buffer);
                        }
                    }
                    FunArgs::Named(args) => {
                        for (i, (name, ty)) in args.iter().enumerate() {
                            if i > 0 {
                                buffer.push_str(", ");
                            }
                            buffer.push_str(name);
                            buffer.push_str(": ");
                            ty.print(buffer);
                        }
                    }
                }
                buffer.push(')');
                if exceptions.is_some() || ret.is_some() {
                    buffer.push_str(": ");
                }
                if let Some(exn) = exceptions {
                    exn.node.print(buffer);
                }
                if let Some(ret) = ret {
                    if exceptions.is_some() {
                        buffer.push(' ');
                    }
                    ret.node.print(buffer);
                }
            }
        }
    }
}

impl FunSig {
    pub fn print(
        &self,
        parent_ty: &Option<L<Id>>,
        name: &Id,
        ty_args: &[Type],
        buffer: &mut String,
    ) {
        if let Some(parent_ty) = parent_ty {
            buffer.push_str(&parent_ty.node);
            buffer.push('.');
        }
        buffer.push_str(name);
        print_ty_args(ty_args, buffer);
        buffer.push('(');
        match &self.self_ {
            SelfParam::No => {}
            SelfParam::Implicit => {
                buffer.push_str("self");
                if !self.params.is_empty() {
                    buffer.push_str(", ");
                }
            }
            SelfParam::Explicit(ty) => {
                buffer.push_str("self: ");
                ty.node.print(buffer);
                if !self.params.is_empty() {
                    buffer.push_str(", ");
                }
            }
        }
        for (i, (param_name, param_ty)) in self.params.iter().enumerate() {
            if i != 0 {
                buffer.push_str(", ");
            }
            buffer.push_str(param_name);
            buffer.push_str(": ");
            param_ty.node.print(buffer);
        }
        buffer.push(')');
        if self.exceptions.is_some() || self.return_ty.is_some() {
            buffer.push_str(": ");
        }
        if let Some(exn) = &self.exceptions {
            exn.node.print(buffer);
        }
        if let Some(ret_ty) = &self.return_ty {
            if self.exceptions.is_some() {
                buffer.push(' ');
            }
            ret_ty.node.print(buffer);
        }
    }
}

impl Stmt {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            Stmt::Break { label, level: _ } => {
                buffer.push_str("break");
                if let Some(label) = label {
                    buffer.push_str(" \'");
                    buffer.push_str(label);
                }
            }

            Stmt::Continue { label, level: _ } => {
                buffer.push_str("continue");
                if let Some(label) = label {
                    buffer.push_str(" \'");
                    buffer.push_str(label);
                }
            }

            Stmt::Let(LetStmt { lhs, rhs }) => {
                buffer.push_str("let ");
                lhs.node.print(buffer);
                buffer.push_str(" = ");
                rhs.node.print(buffer, 0);
            }

            Stmt::Assign(AssignStmt { lhs, rhs, op }) => {
                lhs.node.print(buffer, 0);
                let op_str = match op {
                    AssignOp::Eq => "=",
                    AssignOp::PlusEq => "+=",
                    AssignOp::MinusEq => "-=",
                    AssignOp::StarEq => "*=",
                };
                buffer.push(' ');
                buffer.push_str(op_str);
                buffer.push(' ');
                rhs.node.print(buffer, 0);
            }

            Stmt::Expr(expr) => expr.node.print(buffer, indent),

            Stmt::For(ForStmt {
                pat,
                expr,
                body,
                iter_ty: _,
                item_ty: _,
            }) => {
                buffer.push_str("for ");
                pat.node.print(buffer);
                buffer.push_str(" in ");
                expr.node.print(buffer, 0);
                buffer.push_str(":\n");
                for (i, stmt) in body.iter().enumerate() {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                }
            }

            Stmt::While(WhileStmt { label, cond, body }) => {
                if let Some(label) = label {
                    buffer.push('\'');
                    buffer.push_str(label);
                    buffer.push_str(": ");
                }
                buffer.push_str("while ");
                cond.node.print(buffer, 0);
                buffer.push_str(":\n");
                for (i, stmt) in body.iter().enumerate() {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                }
            }

            Stmt::WhileLet(WhileLetStmt {
                label,
                pat,
                cond,
                body,
            }) => {
                if let Some(label) = label {
                    buffer.push('\'');
                    buffer.push_str(label);
                    buffer.push_str(": ");
                }
                buffer.push_str("while let ");
                pat.node.print(buffer);
                buffer.push_str(" = ");
                cond.node.print(buffer, 0);
                buffer.push_str(":\n");
                for (i, stmt) in body.iter().enumerate() {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                }
            }
        }
    }
}

impl Expr {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            Expr::LocalVar(id) => {
                buffer.push_str(id);
            }

            Expr::TopVar(VarExpr { id, ty_args }) | Expr::Constr(ConstrExpr { id, ty_args }) => {
                buffer.push_str(id);
                print_ty_args(ty_args, buffer);
            }

            Expr::Variant(VariantExpr { id, args }) => {
                buffer.push('~');
                buffer.push_str(id);
                if !args.is_empty() {
                    buffer.push('(');
                    for (i, arg) in args.iter().enumerate() {
                        if i != 0 {
                            buffer.push_str(", ");
                        }
                        if let Some(name) = &arg.name {
                            buffer.push_str(name);
                            buffer.push_str(" = ");
                        }
                        arg.node.node.print(buffer, 0);
                    }
                    buffer.push(')');
                }
            }

            Expr::FieldSelect(FieldSelectExpr { object, field }) => {
                object.node.print(buffer, 0);
                buffer.push('.');
                buffer.push_str(field);
            }

            Expr::MethodSelect(MethodSelectExpr {
                object,
                method_ty_id,
                method_id,
                ty_args,
            }) => {
                object.node.print(buffer, 0);
                buffer.push_str(".{");
                buffer.push_str(method_ty_id);
                buffer.push_str(".}");
                buffer.push_str(method_id);
                print_ty_args(ty_args, buffer);
            }

            Expr::ConstrSelect(ConstrSelectExpr {
                ty,
                constr: member,
                ty_args,
            })
            | Expr::AssocFnSelect(AssocFnSelectExpr {
                ty,
                member,
                ty_args,
            }) => {
                buffer.push_str(ty);
                buffer.push('.');
                buffer.push_str(member);
                print_ty_args(ty_args, buffer);
            }

            Expr::Call(CallExpr { fun, args }) => {
                let parens = !matches!(
                    &fun.node,
                    Expr::LocalVar(_)
                        | Expr::TopVar(_)
                        | Expr::Constr(_)
                        | Expr::FieldSelect(_)
                        | Expr::ConstrSelect(_)
                        | Expr::MethodSelect(_)
                );
                if parens {
                    buffer.push('(');
                }
                fun.node.print(buffer, 0);
                if parens {
                    buffer.push(')');
                }
                buffer.push('(');
                for (i, CallArg { name, expr }) in args.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    expr.node.print(buffer, 0);
                }
                buffer.push(')');
            }

            Expr::Int(IntExpr {
                text,
                suffix,
                radix,
                parsed: _,
            }) => {
                match radix {
                    2 => buffer.push_str("0b"),
                    10 => {}
                    16 => buffer.push_str("0x"),
                    _ => panic!(),
                }
                buffer.push_str(text);
                match suffix {
                    Some(IntKind::I32) => buffer.push_str("I32"),
                    Some(IntKind::U32) => buffer.push_str("U32"),
                    Some(IntKind::I8) => buffer.push_str("I8"),
                    Some(IntKind::U8) => buffer.push_str("U8"),
                    None => {}
                }
            }

            Expr::String(parts) => {
                buffer.push('"');
                for part in parts {
                    match part {
                        StringPart::Str(str) => buffer.push_str(str), // TODO: escaping
                        StringPart::Expr(expr) => {
                            buffer.push('`');
                            expr.node.print(buffer, 0);
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

            Expr::Self_ => buffer.push_str("self"),

            Expr::BinOp(BinOpExpr { left, right, op }) => {
                let left_parens = expr_parens(&left.node);
                let right_parens = expr_parens(&left.node);
                if left_parens {
                    buffer.push('(');
                }
                left.node.print(buffer, 0);
                if left_parens {
                    buffer.push(')');
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
                buffer.push(' ');
                buffer.push_str(op_str);
                buffer.push(' ');
                if right_parens {
                    buffer.push('(');
                }
                right.node.print(buffer, 0);
                if right_parens {
                    buffer.push(')');
                }
            }

            Expr::UnOp(UnOpExpr { op, expr }) => {
                match op {
                    UnOp::Not => buffer.push('!'),
                    UnOp::Neg => buffer.push('-'),
                }
                let parens = expr_parens(&expr.node);
                if parens {
                    buffer.push('(');
                }
                expr.node.print(buffer, 0);
                if parens {
                    buffer.push(')');
                }
            }

            Expr::Record(fields) => {
                buffer.push('(');
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    if let Some(name) = &field.name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    field.node.node.print(buffer, 0);
                }
                buffer.push(')');
            }

            Expr::Return(expr) => {
                buffer.push_str("return ");
                expr.node.print(buffer, 0);
            }

            Expr::Match(MatchExpr { scrutinee, alts }) => {
                buffer.push_str("match ");
                scrutinee.node.print(buffer, 0);
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
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    assert!(guard.is_none()); // TODO
                    pattern.node.print(buffer);
                    buffer.push_str(":\n");
                    for (j, stmt) in rhs.iter().enumerate() {
                        if j != 0 {
                            buffer.push('\n');
                        }
                        buffer.push_str(&INDENTS[0..indent as usize + 8]);
                        stmt.node.print(buffer, indent + 8);
                    }
                }
            }

            Expr::If(IfExpr {
                branches,
                else_branch,
            }) => {
                buffer.push_str("if ");
                branches[0].0.node.print(buffer, 0);
                buffer.push_str(":\n");
                for (i, stmt) in branches[0].1.iter().enumerate() {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                }
                for branch in &branches[1..] {
                    buffer.push('\n');
                    buffer.push_str(&INDENTS[0..indent as usize]);
                    buffer.push_str("elif ");
                    branch.0.node.print(buffer, 0);
                    buffer.push_str(":\n");
                    for (i, stmt) in branch.1.iter().enumerate() {
                        if i != 0 {
                            buffer.push('\n');
                        }
                        buffer.push_str(&INDENTS[0..indent as usize + 4]);
                        stmt.node.print(buffer, indent + 4);
                    }
                }
                if let Some(else_branch) = else_branch {
                    buffer.push('\n');
                    buffer.push_str(&INDENTS[0..indent as usize]);
                    buffer.push_str("else:\n");
                    for (i, stmt) in else_branch.iter().enumerate() {
                        if i != 0 {
                            buffer.push('\n');
                        }
                        buffer.push_str(&INDENTS[0..indent as usize + 4]);
                        stmt.node.print(buffer, indent + 4);
                    }
                }
            }

            Expr::Fn(FnExpr { sig, body }) => {
                buffer.push_str("fn");
                buffer.push('(');
                for (i, (param_name, param_ty)) in sig.params.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    buffer.push_str(param_name);
                    buffer.push_str(": ");
                    param_ty.node.print(buffer);
                }
                buffer.push(')');
                if sig.exceptions.is_some() || sig.return_ty.is_some() {
                    buffer.push_str(": ");
                }
                if let Some(exn) = &sig.exceptions {
                    exn.node.print(buffer);
                }
                if let Some(ret_ty) = &sig.return_ty {
                    if sig.exceptions.is_some() {
                        buffer.push(' ');
                    }
                    ret_ty.node.print(buffer);
                }
                buffer.push('\n');
                for (i, stmt) in body.iter().enumerate() {
                    if i != 0 {
                        buffer.push('\n');
                    }
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                }
            }
        }
    }
}

impl Pat {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Pat::Var(VarPat { var, ty }) => {
                buffer.push_str(var);
                buffer.push_str(": ");
                ty.print(buffer);
            }

            Pat::Constr(ConstrPattern {
                constr: Constructor { type_, constr },
                fields,
                ty_args,
            }) => {
                buffer.push_str(type_);
                if let Some(constr) = constr {
                    buffer.push('.');
                    buffer.push_str(constr);
                }

                print_ty_args(ty_args, buffer);

                if !fields.is_empty() {
                    buffer.push('(');
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
            }

            Pat::Variant(VariantPattern { constr, fields }) => {
                buffer.push_str(constr);
                if !fields.is_empty() {
                    buffer.push('(');
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
            }

            Pat::Record(fields) => {
                buffer.push('(');
                for (i, field) in fields.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    let Named { name, node } = field;
                    if let Some(name) = name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    node.node.print(buffer);
                }
                buffer.push(')');
            }

            Pat::Ignore => buffer.push('_'),

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

            Pat::StrPfx(str, pat) => {
                buffer.push('"');
                buffer.push_str(str); // TODO: escaping
                buffer.push('"');
                buffer.push(' ');
                buffer.push_str(pat);
            }

            Pat::Or(pat1, pat2) => {
                buffer.push('(');
                pat1.node.print(buffer);
                buffer.push_str(") | (");
                pat2.node.print(buffer);
                buffer.push(')');
            }
        }
    }
}

fn expr_parens(expr: &Expr) -> bool {
    !matches!(
        expr,
        Expr::LocalVar(_)
            | Expr::TopVar(_)
            | Expr::Constr(_)
            | Expr::FieldSelect(_)
            | Expr::ConstrSelect(_)
    )
}

fn print_ty_args(args: &[Type], buffer: &mut String) {
    if args.is_empty() {
        return;
    }

    buffer.push('[');
    for (i, ty) in args.iter().enumerate() {
        if i != 0 {
            buffer.push_str(", ");
        }
        buffer.push_str(&ty.to_string());
    }
    buffer.push(']');
}

const INDENTS: &str = "                                                  ";

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
