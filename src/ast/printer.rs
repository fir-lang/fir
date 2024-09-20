use crate::ast::*;

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
        buffer.push_str(self.name.as_str());

        if !self.type_params.is_empty() {
            buffer.push('[');
            for (i, type_param) in self.type_params.iter().enumerate() {
                buffer.push_str(type_param.as_str());
                if i != self.type_params.len() - 1 {
                    buffer.push_str(", ");
                }
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
                    buffer.push_str(&INDENTS[0..indent as usize]);
                    buffer.push_str(constr.name.as_str());
                    match &constr.fields {
                        ConstructorFields::Empty => {}

                        ConstructorFields::Named(fields) => {
                            buffer.push_str(":\n");
                            for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                                buffer.push_str(&INDENTS[0..indent as usize]);
                                buffer.push_str(field_name.as_str());
                                buffer.push_str(": ");
                                field_ty.print(buffer);
                                if i != fields.len() - 1 {
                                    buffer.push('\n');
                                }
                            }
                        }

                        ConstructorFields::Unnamed(fields) => {
                            buffer.push('(');
                            for (i, field_ty) in fields.iter().enumerate() {
                                field_ty.print(buffer);
                                if i != fields.len() - 1 {
                                    buffer.push_str(", ");
                                }
                            }
                            buffer.push(')');
                        }
                    }
                    if i != constrs.len() - 1 {
                        buffer.push('\n');
                    }
                }
            }

            TypeDeclRhs::Product(fields) => match fields {
                ConstructorFields::Empty => {}

                ConstructorFields::Named(fields) => {
                    buffer.push_str(":\n");
                    for (i, (field_name, field_ty)) in fields.iter().enumerate() {
                        buffer.push_str(&INDENTS[0..indent as usize]);
                        buffer.push_str(field_name.as_str());
                        buffer.push_str(": ");
                        field_ty.print(buffer);
                        if i != fields.len() - 1 {
                            buffer.push('\n');
                        }
                    }
                }

                ConstructorFields::Unnamed(fields) => {
                    buffer.push('(');
                    for (i, field_ty) in fields.iter().enumerate() {
                        field_ty.print(buffer);
                        if i != fields.len() - 1 {
                            buffer.push_str(", ");
                        }
                    }
                    buffer.push(')');
                }
            },
        }
    }
}

impl FunDecl {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        self.sig.print(buffer);
        if let Some(body) = &self.body {
            buffer.push_str(" =\n");
            for (i, stmt) in body.node.iter().enumerate() {
                buffer.push_str(&INDENTS[0..indent as usize + 4]);
                stmt.node.print(buffer, indent + 4);
                if i != body.node.len() - 1 {
                    buffer.push('\n');
                }
            }
        }
    }
}

impl ImportDecl {
    pub fn print(&self, buffer: &mut String) {
        buffer.push_str("import ");
        for (i, part) in self.path.iter().enumerate() {
            buffer.push_str(part);
            if i != self.path.len() - 1 {
                buffer.push('.');
            }
        }
    }
}

impl TraitDecl {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        buffer.push_str(&INDENTS[0..indent as usize]);
        buffer.push_str("trait ");
        buffer.push_str(self.name.node.as_str());
        buffer.push('[');
        buffer.push_str(self.ty.node.0.as_str());
        let bounds = &self.ty.node.1;
        if !bounds.is_empty() {
            buffer.push_str(": ");
            for (i, bound) in bounds.iter().enumerate() {
                bound.node.print(buffer);
                if i != bounds.len() - 1 {
                    buffer.push_str(" + ");
                }
            }
        }
        buffer.push_str("]:\n");
        for (i, item) in self.items.iter().enumerate() {
            buffer.push_str(&INDENTS[0..indent as usize + 4]);
            item.node.print(buffer, indent + 4);
            if i != self.items.len() - 1 {
                buffer.push('\n');
            }
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
            buffer.push_str(&INDENTS[0..indent as usize + 4]);
            item.node.print(buffer, indent + 4);
            if i != self.items.len() - 1 {
                buffer.push('\n');
            }
        }
    }
}

impl Type {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Type::Named(NamedType { name, args }) => {
                buffer.push_str(name.as_str());
                if !args.is_empty() {
                    buffer.push('[');
                    for (i, arg) in args.iter().enumerate() {
                        if let Some(name) = &arg.node.0 {
                            buffer.push_str(name.as_str());
                            buffer.push_str(" = ");
                        }
                        arg.node.1.node.print(buffer);
                        if i != args.len() - 1 {
                            buffer.push_str(", ");
                        }
                    }
                    buffer.push(']');
                }
            }

            Type::Record(fields) => {
                buffer.push('(');
                for (i, field) in fields.iter().enumerate() {
                    if let Some(name) = &field.name {
                        buffer.push_str(name.as_str());
                        buffer.push_str(": ");
                    }
                    field.node.print(buffer);
                    if i != fields.len() - 1 {
                        buffer.push_str(", ");
                    }
                }
                buffer.push(')');
            }
        }
    }
}

impl FunSig {
    pub fn print(&self, buffer: &mut String) {
        buffer.push_str("fn ");
        buffer.push_str(self.name.node.as_str());
        if !self.type_params.is_empty() {
            buffer.push('[');
            print_context(&self.type_params, buffer);
            buffer.push(']');
        }
        buffer.push('(');
        if self.self_ {
            buffer.push_str("self");
            if !self.params.is_empty() {
                buffer.push_str(", ");
            }
        }
        for (i, (param_name, param_ty)) in self.params.iter().enumerate() {
            buffer.push_str(param_name.as_str());
            buffer.push_str(": ");
            param_ty.node.print(buffer);
            if i != self.params.len() - 1 {
                buffer.push_str(", ");
            }
        }
        buffer.push(')');
        if let Some(ret_ty) = &self.return_ty {
            buffer.push_str(": ");
            ret_ty.node.print(buffer);
        }
    }
}

impl Stmt {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
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
                body,
            }) => {
                buffer.push_str("for ");
                buffer.push_str(var.as_str());
                assert!(ty.is_none()); // TODO
                buffer.push_str(" in ");
                expr.node.print(buffer, 0);
                buffer.push_str(":\n");
                for (i, stmt) in body.iter().enumerate() {
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                    if i != body.len() - 1 {
                        buffer.push('\n');
                    }
                }
            }

            Stmt::While(WhileStmt { cond, body }) => {
                buffer.push_str("while ");
                cond.node.print(buffer, 0);
                buffer.push_str(":\n");
                for stmt in body {
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                    buffer.push('\n');
                }
            }
        }
    }
}

impl Expr {
    pub fn print(&self, buffer: &mut String, indent: u32) {
        match self {
            Expr::Var(var) | Expr::Constr(var) => buffer.push_str(var.as_str()),

            Expr::FieldSelect(FieldSelectExpr { object, field }) => {
                object.node.print(buffer, 0);
                buffer.push('.');
                buffer.push_str(field.as_str());
            }

            Expr::ConstrSelect(ConstrSelectExpr { ty, constr }) => {
                buffer.push_str(ty.as_str());
                buffer.push('.');
                buffer.push_str(constr.as_str());
            }

            Expr::Call(CallExpr { fun, args }) => {
                let parens = !matches!(
                    &fun.node,
                    Expr::Var(_) | Expr::Constr(_) | Expr::FieldSelect(_) | Expr::ConstrSelect(_)
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
                    if let Some(name) = name {
                        buffer.push_str(name.as_str());
                        buffer.push_str(" = ");
                    }
                    expr.node.print(buffer, 0);
                    if i != args.len() - 1 {
                        buffer.push_str(", ");
                    }
                }
                buffer.push(')');
            }

            Expr::Range(RangeExpr {
                from,
                to,
                inclusive,
            }) => {
                from.node.print(buffer, 0);
                if *inclusive {
                    buffer.push_str("..=");
                } else {
                    buffer.push_str("..");
                }
                to.node.print(buffer, 0);
            }

            Expr::Int(int) => match int {
                IntExpr::I8(i) => {
                    buffer.push_str(&i.to_string());
                    buffer.push_str("i8");
                }
                IntExpr::U8(i) => {
                    buffer.push_str(&i.to_string());
                    buffer.push_str("u8");
                }
                IntExpr::I32(i) => {
                    buffer.push_str(&i.to_string());
                    buffer.push_str("i32");
                }
                IntExpr::U32(i) => {
                    buffer.push_str(&i.to_string());
                    buffer.push_str("u32");
                }
            },

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
                    BinOp::Lt => "<",
                    BinOp::Gt => ">",
                    BinOp::LtEq => "<=",
                    BinOp::GtEq => ">=",
                    BinOp::And => "&&",
                    BinOp::Or => "||",
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

            Expr::ArrayIndex(_) => todo!(),

            Expr::Record(fields) => {
                buffer.push('(');
                for (i, field) in fields.iter().enumerate() {
                    if let Some(name) = &field.name {
                        buffer.push_str(name);
                        buffer.push_str(" = ");
                    }
                    field.node.node.print(buffer, 0);
                    if i != fields.len() - 1 {
                        buffer.push_str(", ");
                    }
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
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    assert!(guard.is_none()); // TODO
                    pattern.node.print(buffer);
                    buffer.push_str(":\n");
                    for (j, stmt) in rhs.iter().enumerate() {
                        buffer.push_str(&INDENTS[0..indent as usize + 8]);
                        stmt.node.print(buffer, indent + 8);
                        if j != rhs.len() - 1 {
                            buffer.push('\n');
                        }
                    }
                    if i != alts.len() - 1 {
                        buffer.push('\n');
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
                    buffer.push_str(&INDENTS[0..indent as usize + 4]);
                    stmt.node.print(buffer, indent + 4);
                    if i != branches[0].1.len() - 1 {
                        buffer.push('\n');
                    }
                }
                for branch in &branches[1..] {
                    buffer.push_str("elif ");
                    branch.0.node.print(buffer, 0);
                    buffer.push_str(":\n");
                    for (i, stmt) in branch.1.iter().enumerate() {
                        buffer.push_str(&INDENTS[0..indent as usize + 4]);
                        stmt.node.print(buffer, indent + 4);
                        if i != branch.1.len() - 1 {
                            buffer.push('\n');
                        }
                    }
                }
                if let Some(else_branch) = else_branch {
                    buffer.push_str("else:\n");
                    for (i, stmt) in else_branch.iter().enumerate() {
                        buffer.push_str(&INDENTS[0..indent as usize + 4]);
                        stmt.node.print(buffer, indent + 4);
                        if i != else_branch.len() - 1 {
                            buffer.push('\n');
                        }
                    }
                }
            }

            Expr::Instantiation(path, tys) => {
                match path {
                    Path::TopLevel { fun_id } => {
                        buffer.push_str(fun_id.as_str());
                    }

                    Path::Constructor {
                        ty_id,
                        constr_id: member_id,
                    }
                    | Path::AssociatedFn {
                        ty_id,
                        fun_id: member_id,
                    } => {
                        buffer.push_str(ty_id.as_str());
                        buffer.push('.');
                        buffer.push_str(member_id.as_str());
                    }

                    Path::Method {
                        receiver,
                        receiver_ty,
                        method_id,
                    } => {
                        buffer.push('(');
                        receiver.print(buffer, indent + 4);
                        buffer.push_str(" : ");
                        buffer.push_str(&receiver_ty.to_string());
                        buffer.push(')');
                        buffer.push('.');
                        buffer.push_str(method_id.as_str());
                    }
                }
                buffer.push('[');
                for (i, ty) in tys.iter().enumerate() {
                    buffer.push_str(&ty.to_string());
                    if i != tys.len() - 1 {
                        buffer.push_str(", ");
                    }
                }
                buffer.push(']');
            }
        }
    }
}

impl Pat {
    pub fn print(&self, buffer: &mut String) {
        match self {
            Pat::Var(var) => buffer.push_str(var.as_str()),

            Pat::Constr(ConstrPattern {
                constr: Constructor { type_, constr },
                fields,
            }) => {
                buffer.push_str(type_.as_str());
                if let Some(constr) = constr {
                    buffer.push('.');
                    buffer.push_str(constr.as_str());
                }

                if !fields.is_empty() {
                    buffer.push('(');
                    for (i, field) in fields.iter().enumerate() {
                        if let Some(name) = &field.name {
                            buffer.push_str(name.as_str());
                            buffer.push_str(" = ");
                        }
                        field.node.node.print(buffer);
                        if i != fields.len() - 1 {
                            buffer.push_str(", ");
                        }
                    }
                    buffer.push(')');
                }
            }

            Pat::Record(_) => todo!(),

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
                buffer.push_str(&INDENTS[0..indent as usize]);
                buffer.push_str("type ");
                buffer.push_str(ty.as_str());
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
                buffer.push_str(name.as_str());
                buffer.push_str(" = ");
                ty.node.print(buffer);
            }
            ImplDeclItem::Fun(fun_decl) => fun_decl.print(buffer, indent),
        }
    }
}

fn print_context(context: &[L<(L<Id>, Vec<L<Type>>)>], buffer: &mut String) {
    for (i, ty) in context.iter().enumerate() {
        buffer.push_str(ty.node.0.node.as_str());
        if !ty.node.1.is_empty() {
            buffer.push_str(": ");
            for (j, bound) in ty.node.1.iter().enumerate() {
                bound.node.print(buffer);
                if j != ty.node.1.len() - 1 {
                    buffer.push_str(" + ");
                }
            }
        }
        if i != context.len() - 1 {
            buffer.push_str(", ");
        }
    }
}

fn expr_parens(expr: &Expr) -> bool {
    !matches!(
        expr,
        Expr::Var(_) | Expr::Constr(_) | Expr::FieldSelect(_) | Expr::ConstrSelect(_)
    )
}

const INDENTS: &str = "                                                  ";
