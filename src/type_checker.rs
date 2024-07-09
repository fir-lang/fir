#![allow(unused)]

use crate::ast;
use crate::collections::{Map, Set};
use crate::scope_map::ScopeMap;

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use smol_str::SmolStr;

// Syntax for type checking types.

// Use AST id type for now to avoid a renaming pass.
type Id = SmolStr;

/// A type scheme.
#[derive(Debug)]
struct Scheme {
    /// Generalized variables, e.g. `T` in the scheme for `fn id[T](a: T): T = a`.
    ///
    /// `Vec` instead of `Set` as type arguments in explicit type applications are ordered.
    ///
    /// For now, all quantified variables have kind `*`.
    quantified_vars: Vec<Id>,

    /// Predicates, e.g. `Eq[T]` in the type scheme for
    ///
    ///   fn linearSearch[T][Eq[T]](vec: Vec[T], elem: T): Option[Usize] = ...
    ///
    preds: Vec<Ty>,

    /// The generalized type.
    ty: Ty,

    /// Source code location of the variable with this type scheme. This is used in error messages
    /// and for debugging.
    loc: ast::Loc,
}

/// A type checking type.
#[derive(Debug, Clone)]
enum Ty {
    /// A type constructor, e.g. `Vec`, `Option`, `U32`.
    Con(Id),

    /// A unification variable, created by a type scheme when instantiated.
    Var(TyVarRef),

    /// A type application, e.g. `Vec[U32]`, `Result[E, T]`.
    ///
    /// Because type variables have kind `*`, the constructor can only be a type constructor.
    ///
    /// Invariant: the vector is not empty.
    App(Id, Vec<Ty>),

    /// A record type, e.g. `(x: U32, y: U32)`.
    Record(Map<Id, Ty>),

    /// Only in type schemes: a quantified type variable.
    ///
    /// Instantiation converts these into unification variables (`Ty::Var`).
    QVar(Id),

    /// A function type, e.g. `Fn(U32): Str`.
    Fun(Vec<Ty>, Box<Ty>),

    /// A function type with named arguments, e.g. `Fn(x: U32, y: U32): Str`.
    FunNamedArgs(Map<Id, Ty>, Box<Ty>),
}

#[derive(Debug, Clone)]
struct TyVarRef(Rc<TyVar>);

#[derive(Debug, Clone)]
struct TyVar {
    /// Identity of the unification variable.
    ///
    /// This is used to compare unification variables for equality.
    id: u32,

    /// Depth of the scope the unification variable was craeted in.
    level: Cell<u32>,

    /// When unified with a type, this holds the type.
    link: RefCell<Option<Ty>>,

    /// Source code location of the type scheme that generated this type variable. This is used in
    /// error messages and for debugging.
    loc: ast::Loc,
}

impl TyVarRef {
    fn id(&self) -> u32 {
        self.0.id
    }

    fn level(&self) -> u32 {
        self.0.level.get()
    }

    fn link(&self) -> Option<Ty> {
        self.0.link.borrow().clone()
    }

    fn set_link(&self, ty: Ty) {
        *self.0.link.borrow_mut() = Some(ty);
    }

    fn prune_level(&self, level: u32) {
        let self_level = self.level();
        self.0.level.set(std::cmp::min(level, self_level));
    }
}

#[derive(Debug, Default)]
struct TyVarGen {
    next_id: u32,
}

impl TyVarGen {
    fn new_var(&mut self, level: u32, loc: ast::Loc) -> TyVarRef {
        let id = self.next_id;
        self.next_id += 1;
        TyVarRef(Rc::new(TyVar {
            id,
            level: Cell::new(level),
            link: RefCell::new(None),
            loc,
        }))
    }
}

/// A type constructor.
#[derive(Debug, Clone, PartialEq, Eq)]
struct TyCon {
    id: Id,

    /// Type constructor arity.
    ///
    /// Because all type variables have kind `*` we don't need the kind information.
    arity: u32,
}

struct RecordTyCon {}

#[derive(Debug, Clone, PartialEq, Eq)]
enum TyConArgs {
    Unnamed { arity: u32 },
    Named { names: Set<Id> },
}

/// Type constructors and types in the program.
#[derive(Debug)]
struct PgmTypes {
    /// Type schemes of top-level values.
    top_schemes: Map<Id, Scheme>,

    /// Type schemes of associated functions.
    associated_schemes: Map<Id, Map<Id, Scheme>>,

    /// Type constructor details.
    cons: Map<Id, TyCon>,
}

fn collect_types(module: &ast::Module) -> PgmTypes {
    let cons = collect_cons(module);
    let (top_schemes, associated_schemes) = collect_schemes(module, &cons);
    PgmTypes {
        top_schemes,
        associated_schemes,
        cons,
    }
}

fn collect_cons(module: &ast::Module) -> Map<Id, TyCon> {
    let mut cons: Map<Id, TyCon> = Default::default();

    for decl in module {
        let ty_decl = match &decl.node {
            ast::TopDecl::Type(ty) => ty,

            ast::TopDecl::Fun(_) => continue,

            ast::TopDecl::Import(_) => {
                // Imports should've been resolved at this point.
                panic!("Import declaration in type checker")
            }
        };

        if cons.contains_key(&ty_decl.node.name) {
            panic!("Type {} is defined multiple times", ty_decl.node.name);
        }

        cons.insert(
            ty_decl.node.name.clone(),
            TyCon {
                id: ty_decl.node.name.clone(),
                arity: ty_decl.node.type_params.len() as u32,
            },
        );
    }

    cons
}

fn collect_schemes(
    module: &ast::Module,
    ty_cons: &Map<Id, TyCon>,
) -> (Map<Id, Scheme>, Map<Id, Map<Id, Scheme>>) {
    let mut top_schemes: Map<Id, Scheme> = Default::default();
    let mut associated_schemes: Map<Id, Map<Id, Scheme>> = Default::default();

    for decl in module {
        let ast::FunDecl {
            type_name,
            name,
            type_params,
            predicates,
            params,
            return_ty,
            ..
        } = match &decl.node {
            ast::TopDecl::Type(_) => continue,

            ast::TopDecl::Fun(f) => &f.node,

            ast::TopDecl::Import(_) => {
                // Imports should've been resolved at this point.
                panic!("Import declaration in type checker")
            }
        };

        // If associated function: check that the type exists.
        if let Some(type_name) = type_name {
            if !ty_cons.contains_key(&type_name.node) {
                panic!(
                    "Type {} of associated function at {} is not defined",
                    type_name.node,
                    loc_string(&decl.loc)
                );
            }
        }

        // Check duplicate type and term arguments.
        let mut ty_arg_names: Set<Id> = Default::default();
        for ty_arg_name in type_params {
            let new = ty_arg_names.insert(ty_arg_name.node.clone());
            if !new {
                panic!(
                    "Type parameter {} at {} is defined multiple times",
                    ty_arg_name.node,
                    loc_string(&ty_arg_name.loc)
                );
            }
        }

        let mut val_arg_names: Set<Id> = Default::default();
        for val_arg_name in params {
            let new = val_arg_names.insert(val_arg_name.0.clone());
            if !new {
                panic!(
                    "Parameter {} at {} is defined multiple times",
                    val_arg_name.0,
                    loc_string(&decl.loc)
                );
            }
        }

        let quantified_vars: Vec<Id> = type_params.iter().map(|param| param.node.clone()).collect();

        let preds: Vec<Ty> = predicates
            .iter()
            .map(|pred| convert_ast_ty(ty_cons, &pred.node, &pred.loc))
            .collect();

        let arg_tys: Vec<Ty> = params
            .iter()
            .map(|ty| convert_ast_ty(ty_cons, &ty.1.node, &ty.1.loc))
            .collect();

        let ret_ty = match return_ty {
            Some(ret_ty) => convert_ast_ty(ty_cons, &ret_ty.node, &ret_ty.loc),
            None => Ty::Record(Default::default()), // unit
        };

        let fun_ty = Ty::App(fun_ty_con(arg_tys.len() as u32), arg_tys);

        let scheme = Scheme {
            quantified_vars,
            preds,
            ty: fun_ty,
            loc: decl.loc.clone(),
        };

        match type_name {
            Some(ty_name) => {
                let old = associated_schemes
                    .entry(ty_name.node.clone())
                    .or_default()
                    .insert(name.node.clone(), scheme);

                if old.is_some() {
                    panic!(
                        "Associated function {}.{} is defined multiple times at {}",
                        ty_name.node,
                        name.node,
                        loc_string(&decl.loc)
                    );
                }
            }
            None => {
                let old = top_schemes.insert(name.node.clone(), scheme);

                if old.is_some() {
                    panic!(
                        "Function {} is defined multiple times at {}",
                        name.node,
                        loc_string(&decl.loc)
                    );
                }
            }
        }
    }

    (top_schemes, associated_schemes)
}

/// Convert an AST type to a type checking type.
fn convert_ast_ty(ty_cons: &Map<Id, TyCon>, ast_ty: &ast::Type, loc: &ast::Loc) -> Ty {
    match ast_ty {
        ast::Type::Named(ast::NamedType { name, args }) => match ty_cons.get(name) {
            Some(con) => {
                if con.arity as usize != args.len() {
                    panic!(
                        "Incorrect number of type arguments at {}, expected {} type arguments, found {}",
                        loc_string(loc), con.arity, args.len()
                    )
                }

                let args: Vec<Ty> = args
                    .iter()
                    .map(|ty| convert_ast_ty(ty_cons, &ty.node, &ty.loc))
                    .collect();

                if args.is_empty() {
                    Ty::Con(name.clone())
                } else {
                    Ty::App(name.clone(), args)
                }
            }
            None => {
                panic!("Unknown type {} at {}", name, loc_string(loc))
            }
        },

        ast::Type::Record(_) => todo!(),
    }
}

// TODO: Cache these.
// TODO: These need to be added to `PgmTypes`.
fn fun_ty_con(arity: u32) -> Id {
    format!("#FUN_{}", arity).into()
}

fn loc_string(loc: &ast::Loc) -> String {
    format!(
        "{}:{}:{}",
        loc.module,
        loc.line_start + 1,
        loc.col_start + 1
    )
}

fn check_fun(fun: &ast::FunDecl, tys: &PgmTypes) {}

impl Scheme {
    fn instantiate(&self, level: u32, var_gen: &mut TyVarGen) -> (Vec<Ty>, Ty) {
        // TODO: We should rename type variables in a renaming pass, or disallow shadowing, or
        // handle shadowing here.

        let var_map: Map<Id, TyVarRef> = self
            .quantified_vars
            .iter()
            .map(|var| (var.clone(), var_gen.new_var(level, self.loc.clone())))
            .collect();

        let preds: Vec<Ty> = self
            .preds
            .iter()
            .map(|pred| pred.subst_qvars(&var_map))
            .collect();

        let ty = self.ty.subst_qvars(&var_map);

        (preds, ty)
    }
}

impl Ty {
    fn subst_qvars(&self, vars: &Map<Id, TyVarRef>) -> Ty {
        match self {
            Ty::Con(con) => Ty::Con(con.clone()),

            Ty::Var(var) => Ty::Var(var.clone()),

            Ty::App(ty, tys) => Ty::App(
                ty.clone(),
                tys.iter().map(|ty| ty.subst_qvars(vars)).collect(),
            ),

            Ty::Record(_) => todo!(),

            Ty::QVar(id) => Ty::Var(vars.get(id).cloned().unwrap()),

            Ty::Fun(args, ret) => Ty::Fun(
                args.iter().map(|arg| arg.subst_qvars(vars)).collect(),
                Box::new(ret.subst_qvars(vars)),
            ),

            Ty::FunNamedArgs(args, ret) => Ty::FunNamedArgs(
                args.iter()
                    .map(|(name, ty)| (name.clone(), ty.subst_qvars(vars)))
                    .collect(),
                Box::new(ret.subst_qvars(vars)),
            ),
        }
    }
}

fn unify(ty1: &Ty, ty2: &Ty, loc: &ast::Loc) {
    match (ty1, ty2) {
        (Ty::Con(con1), Ty::Con(con2)) => {
            if con1 != con2 {
                panic!(
                    "Unable to unify types {} and {} at {}",
                    con1,
                    con2,
                    loc_string(loc)
                )
            }
        }

        (Ty::App(con1, args1), Ty::App(con2, args2)) => {
            if con1 != con2 {
                panic!(
                    "Unable to unify types {} and {} at {}",
                    con1,
                    con2,
                    loc_string(loc)
                )
            }

            // Kinds should've been checked.
            assert_eq!(args1.len(), args2.len());

            for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                unify(arg1, arg2, loc);
            }
        }

        (Ty::QVar(_), _) | (_, Ty::QVar(_)) => {
            panic!("QVar in unification at {}", loc_string(loc));
        }

        (Ty::Var(var1), Ty::Var(var2)) => {
            if var1.id() == var2.id() {
                return;
            }

            let var1_level = var1.level();
            let var2_level = var2.level();

            // We've normalized the types, so the links must be followed to the end.
            debug_assert!(var1.link().is_none());
            debug_assert!(var2.link().is_none());

            // Links must increase in level so that we can follow them to find the level of the
            // group.
            if var1_level < var2_level {
                link_var(var1, ty2);
            } else {
                link_var(var2, ty1);
            }
        }

        (Ty::Var(var), ty2) => link_var(var, ty2),

        (ty1, Ty::Var(var)) => link_var(var, ty1),

        (ty1, ty2) => panic!(
            "Unable to unify types {:?} and {:?} at {}",
            ty1,
            ty2,
            loc_string(loc)
        ),
    }
}

fn link_var(var: &TyVarRef, ty: &Ty) {
    // TODO: Occurs check.
    prune_level(ty, var.level());
    var.set_link(ty.clone());
}

fn prune_level(ty: &Ty, max_level: u32) {
    match ty {
        Ty::Con(_) => {}

        Ty::Var(var) => {
            assert!(var.link().is_none());
            var.prune_level(max_level);
        }

        Ty::App(_, tys) => {
            for ty in tys {
                prune_level(ty, max_level);
            }
        }

        Ty::Record(_) => todo!(),

        Ty::QVar(_) => panic!("QVar in prune_level"),

        Ty::Fun(args, ret) => {
            for arg in args {
                prune_level(arg, max_level);
            }
            prune_level(ret, max_level);
        }

        Ty::FunNamedArgs(args, ret) => {
            for arg in args.values() {
                prune_level(arg, max_level);
            }
            prune_level(ret, max_level);
        }
    }
}

fn check_stmts(
    stmts: &[ast::L<ast::Stmt>],
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
) -> (Vec<Ty>, Ty) {
    todo!()
}

// TODO: Level is the same as the length of `env`, maybe remove the parameter?
fn check_stmt(
    stmt: &ast::L<ast::Stmt>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
) -> (Vec<Ty>, Ty) {
    match &stmt.node {
        ast::Stmt::Let(_) => todo!(),

        ast::Stmt::Assign(_) => todo!(),

        ast::Stmt::Expr(_) => todo!(),

        ast::Stmt::For(_) => todo!(),

        ast::Stmt::While(_) => todo!(),
    }
}

// TODO: When `expected_ty` is available should we unify with the expected type, or should the call
// site do it?
fn check_expr(
    expr: &ast::L<ast::Expr>,
    expected_ty: Option<&Ty>,
    return_ty: &Ty,
    level: u32,
    env: &mut ScopeMap<Id, Ty>,
    var_gen: &mut TyVarGen,
    tys: &PgmTypes,
) -> (Vec<Ty>, Ty) {
    let mut preds: Vec<Ty> = vec![];

    match &expr.node {
        ast::Expr::Var(var) => {
            // Check if local.
            if let Some(ty) = env.get(var) {
                return (vec![], ty.clone());
            }

            if let Some(scheme) = tys.top_schemes.get(var) {
                return scheme.instantiate(level, var_gen);
            }

            panic!("Unbound variable at {}", loc_string(&expr.loc));
        }

        ast::Expr::UpperVar(_) => todo!(),

        ast::Expr::FieldSelect(_) => todo!(),

        ast::Expr::ConstrSelect(_) => todo!(),

        ast::Expr::Call(ast::CallExpr { fun, args }) => {
            let (fun_preds, fun_ty) = check_expr(fun, None, return_ty, level, env, var_gen, tys);
            preds.extend(fun_preds);

            match fun_ty {
                Ty::Fun(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_string(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    for arg in args {
                        if arg.name.is_some() {
                            panic!(
                                "{}: Named argument applied to function that expects positional arguments",
                                loc_string(&expr.loc),
                            );
                        }
                    }

                    let mut arg_tys: Vec<Ty> = Vec::with_capacity(args.len());
                    for (param_ty, arg) in param_tys.iter().zip(args.iter()) {
                        let (arg_preds, arg_ty) = check_expr(
                            &arg.expr,
                            Some(param_ty),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            tys,
                        );
                        preds.extend(arg_preds.into_iter());
                        arg_tys.push(arg_ty);
                    }

                    for (param_ty, arg_ty) in param_tys.iter().zip(arg_tys.iter()) {
                        unify(param_ty, arg_ty, &expr.loc);
                    }

                    (preds, *ret_ty)
                }

                Ty::FunNamedArgs(param_tys, ret_ty) => {
                    if param_tys.len() != args.len() {
                        panic!(
                            "{}: Function with arity {} is passed {} args",
                            loc_string(&expr.loc),
                            param_tys.len(),
                            args.len()
                        );
                    }

                    for arg in args {
                        if arg.name.is_none() {
                            panic!(
                                "{}: Positional argument applied to function that expects named arguments",
                                loc_string(&expr.loc),
                            );
                        }
                    }

                    let param_names: Set<&SmolStr> = param_tys.keys().collect();
                    let arg_names: Set<&SmolStr> =
                        args.iter().map(|arg| arg.name.as_ref().unwrap()).collect();

                    if param_names != arg_names {
                        panic!(
                            "{}: Function expects arguments with names {:?}, but passed {:?}",
                            loc_string(&expr.loc),
                            param_names,
                            arg_names
                        );
                    }

                    for arg in args {
                        let arg_name: &SmolStr = arg.name.as_ref().unwrap();
                        let param_ty: &Ty = param_tys.get(arg_name).unwrap();
                        let (arg_preds, arg_ty) = check_expr(
                            &arg.expr,
                            Some(param_ty),
                            return_ty,
                            level,
                            env,
                            var_gen,
                            tys,
                        );
                        preds.extend(arg_preds.into_iter());
                        unify(&arg_ty, param_ty, &expr.loc);
                    }

                    (preds, *ret_ty)
                }

                _ => panic!(
                    "{}: Function in function application is not a function: {:?}",
                    loc_string(&expr.loc),
                    fun_ty,
                ),
            }
        }

        ast::Expr::Range(_) => todo!(),

        ast::Expr::Int(_) => (vec![], Ty::Con(SmolStr::new_static("I32"))),

        ast::Expr::String(_) => (vec![], Ty::Con(SmolStr::new_static("Str"))),

        ast::Expr::Char(_) => (vec![], Ty::Con(SmolStr::new_static("Char"))),

        ast::Expr::Self_ => todo!(),

        ast::Expr::BinOp(_) => todo!(),

        ast::Expr::UnOp(_) => todo!(),

        ast::Expr::ArrayIndex(_) => todo!(),

        ast::Expr::Record(_) => todo!(),

        ast::Expr::Return(_) => todo!(),

        ast::Expr::Match(_) => todo!(),

        ast::Expr::If(ast::IfExpr {
            branches,
            else_branch,
        }) => {
            let mut branch_tys: Vec<Ty> = Vec::with_capacity(branches.len() + 1);

            for (cond, body) in branches {
                let (cond_preds, cond_ty) = check_expr(
                    cond,
                    Some(&Ty::Con(SmolStr::new_static("Bool"))),
                    return_ty,
                    level,
                    env,
                    var_gen,
                    tys,
                );
                unify(&cond_ty, &Ty::Con(SmolStr::new_static("Bool")), &expr.loc);
                preds.extend(cond_preds);

                let (body_preds, body_ty) =
                    check_stmts(body, expected_ty, return_ty, level, env, var_gen, tys);
                preds.extend(body_preds);

                branch_tys.push(body_ty);
            }

            match else_branch {
                Some(else_body) => {
                    let (body_preds, body_ty) =
                        check_stmts(else_body, expected_ty, return_ty, level, env, var_gen, tys);
                    preds.extend(body_preds);
                    branch_tys.push(body_ty);
                }
                None => {
                    // A bit hacky: ensure that without an else branch the expression returns unit.
                    branch_tys.push(Ty::Record(Default::default()));
                }
            }

            for ty_pair in branch_tys.windows(2) {
                unify(&ty_pair[0], &ty_pair[1], &expr.loc);
            }

            (preds, branch_tys.pop().unwrap())
        }
    }
}
