use crate::ast::*;

pub fn print_module(module: &[L<TopDecl>]) {
    let mut buffer = String::new();
    for (i, top_decl) in module.iter().enumerate() {
        if i != 0 {
            println!();
        }
        top_decl.node.print(&mut buffer, 0);
        println!("{}", buffer);
        buffer.clear();
    }
}

impl TopDecl {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            TopDecl::Type(decl) => decl.node.print(buffer, indent),
            TopDecl::Fun(decl) => decl.node.print(buffer, indent),
            TopDecl::Import(decl) => decl.node.print(buffer),
            TopDecl::Trait(decl) => decl.node.print(buffer, indent),
            TopDecl::Impl(decl) => decl.node.print(buffer, indent),
        }
    }
}

impl TypeDecl {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        buffer.push_str("type ");
        buffer.push_str(&self.name);

        if !self.type_params.is_empty() {
            buffer.push('[');
            for (i, type_param) in self.type_params.iter().enumerate() {
                if i != 0 {
                    buffer.push_str(", ");
                }
                buffer.push_str(type_param);
            }
            buffer.push(']');
        }

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
    pub fn print(&self, buffer: &mut String, indent: u32) {
        if self.body.is_none() {
            buffer.push_str("prim ");
        }
        self.sig.print(&self.name.node, buffer);
        if let Some(body) = &self.body {
            buffer.push_str(" =\n");
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

impl ImportDecl {
    pub fn print(&self, buffer: &mut String) {
        buffer.push_str("import ");
        for (i, part) in self.path.iter().enumerate() {
            if i != 0 {
                buffer.push('.');
            }
            buffer.push_str(part);
        }
    }
}

impl TraitDecl {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        buffer.push_str(&INDENTS[0..indent as usize]);
        buffer.push_str("trait ");
        buffer.push_str(&self.name.node);
        buffer.push('[');
        buffer.push_str(&self.ty.id.node);
        let bounds = &self.ty.bounds;
        if !bounds.is_empty() {
            buffer.push_str(": ");
            for (i, bound) in bounds.iter().enumerate() {
                if i != 0 {
                    buffer.push_str(" + ");
                }
                bound.node.print(buffer);
            }
        }
        buffer.push_str("]:\n");
        for (i, item) in self.items.iter().enumerate() {
            if i != 0 {
                buffer.push('\n');
            }
            buffer.push_str(&INDENTS[0..indent as usize + 4]);
            item.node.print(buffer, indent + 4);
        }
    }
}

impl ImplDecl {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        buffer.push_str("impl");
        if !self.context.is_empty() {
            buffer.push('[');
            print_context(&self.context, buffer);
            buffer.push(']');
        }
        buffer.push(' ');
        self.ty.node.print(buffer);
        buffer.push_str(":\n");
        for (i, item) in self.items.iter().enumerate() {
            if i != 0 {
                buffer.push('\n');
                buffer.push('\n');
            }
            buffer.push_str(&INDENTS[0..indent as usize + 4]);
            item.node.print(buffer, indent + 4);
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
                        if let Some(name) = &arg.node.0 {
                            buffer.push_str(name);
                            buffer.push_str(" = ");
                        }
                        arg.node.1.node.print(buffer);
                    }
                    buffer.push(']');
                }
            }

            Type::Var(var) => buffer.push_str(var),

            Type::Record { fields, extension } => {
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
                if let Some(extension) = extension {
                    buffer.push('|');
                    buffer.push_str(extension);
                }
                buffer.push(')');
            }

            Type::Variant { alts, extension } => {
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
                if let Some(ext) = extension {
                    if !alts.is_empty() {
                        buffer.push_str(", ");
                    }
                    buffer.push_str("..");
                    buffer.push_str(ext);
                }
                buffer.push(']');
            }

            Type::Fn(FnType {
                args,
                ret,
                exceptions,
            }) => {
                buffer.push_str("Fn(");
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        buffer.push_str(", ");
                    }
                    arg.node.print(buffer);
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
    pub fn print(&self, name: &Id, buffer: &mut String) {
        buffer.push_str("fn ");
        buffer.push_str(name);
        if !self.type_params.is_empty() {
            buffer.push('[');
            print_context(&self.type_params, buffer);
            buffer.push(']');
        }
        buffer.push('(');
        match &self.self_ {
            SelfParam::No => {}
            SelfParam::Inferred => {
                buffer.push_str("self");
                if !self.params.is_empty() {
                    buffer.push_str(", ");
                }
            }
            SelfParam::Explicit(ty) => {
                buffer.push_str("self: ");
                ty.print(buffer);
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
            Stmt::Break => {
                buffer.push_str("break");
            }

            Stmt::Continue => {
                buffer.push_str("continue");
            }

            Stmt::Let(LetStmt { lhs, ty, rhs }) => {
                buffer.push_str("let ");
                lhs.node.print(buffer);
                if let Some(ty) = ty {
                    buffer.push_str(": ");
                    ty.node.print(buffer);
                }
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
                var,
                ty,
                expr,
                expr_ty: _,
                body,
            }) => {
                buffer.push_str("for ");
                buffer.push_str(var);
                assert!(ty.is_none()); // TODO
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

            Stmt::While(WhileStmt { cond, body }) => {
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
        }
    }
}

impl Expr {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            Expr::Var(VarExpr { id, ty_args }) | Expr::Constr(ConstrExpr { id, ty_args }) => {
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
                object_ty: _,
                method,
                ty_args,
            }) => {
                object.node.print(buffer, 0);
                buffer.push('.');
                buffer.push_str(method);
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
                    Expr::Var(_)
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

            Expr::Fn(_) => todo!(),
        }
    }
}

impl Pat {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Pat::Var(var) => buffer.push_str(var),

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

                if !ty_args.is_empty() {
                    buffer.push('[');
                    for (i, ty_arg) in ty_args.iter().enumerate() {
                        if i != 0 {
                            buffer.push_str(", ");
                        }
                        buffer.push_str(&ty_arg.to_string());
                    }
                    buffer.push(']');
                }

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

impl TraitDeclItem {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            TraitDeclItem::AssocTy(ty) => {
                buffer.push_str("type ");
                buffer.push_str(ty);
            }
            TraitDeclItem::Fun(ty) => {
                ty.print(buffer, indent);
            }
        }
    }
}

impl ImplDeclItem {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            ImplDeclItem::AssocTy(AssocTyDecl { name, ty }) => {
                buffer.push_str("type ");
                buffer.push_str(name);
                buffer.push_str(" = ");
                ty.node.print(buffer);
            }
            ImplDeclItem::Fun(fun_decl) => fun_decl.print(buffer, indent),
        }
    }
}

fn print_context(context: &[TypeParam], buffer: &mut String) {
    for (i, ty) in context.iter().enumerate() {
        if i != 0 {
            buffer.push_str(", ");
        }
        buffer.push_str(&ty.id.node);
        if !ty.bounds.is_empty() {
            buffer.push_str(": ");
            for (j, bound) in ty.bounds.iter().enumerate() {
                if j != 0 {
                    buffer.push_str(" + ");
                }
                bound.node.print(buffer);
            }
        }
    }
}

fn print_ty_args(args: &[Ty], buffer: &mut String) {
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

fn expr_parens(expr: &Expr) -> bool {
    !matches!(
        expr,
        Expr::Var(_) | Expr::Constr(_) | Expr::FieldSelect(_) | Expr::ConstrSelect(_)
    )
}

const INDENTS: &str = "                                                  ";
