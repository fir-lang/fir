#![allow(unused)]

use crate::ast;
use crate::collections::{Map, Set};

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
}

/// A type checking type.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Ty {
    /// A type constructor, e.g. `Vec`, `Option`, `U32`.
    Con(Id),

    /// A type variable, e.g. `A` where `A` is not a constructor.
    Var(Id),

    /// A type application, e.g. `Vec[U32]`, `Result[E, T]`.
    ///
    /// Because type variables have kind `*`, the constructor can only be a type constructor.
    App(Id, Vec<Ty>),

    /// A record type, e.g. `(x: U32, y: U32)`.
    Record(Map<Id, Ty>),

    /// Only in type schemes: a quantified variable.
    QVar(Id),
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
    todo!()
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
            ..
        } = match &decl.node {
            ast::TopDecl::Type(_) => continue,

            ast::TopDecl::Fun(f) => &f.node,

            ast::TopDecl::Import(_) => {
                // Imports should've been resolved at this point.
                panic!("Import declaration in type checker")
            }
        };
    }

    todo!()
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

                Ty::App(name.clone(), args)
            }
            None => {
                panic!("Unknown type {} at {}", name, loc_string(loc))
            }
        },
        ast::Type::Record(_) => todo!(),
    }
}

fn loc_string(loc: &ast::Loc) -> String {
    format!(
        "{}:{}:{}",
        loc.module,
        loc.line_start + 1,
        loc.col_start + 1
    )
}
