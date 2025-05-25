#![allow(clippy::enum_variant_names)]

pub mod printer;

use crate::collections::Map;
use crate::interpolation::StringPart;
pub use crate::token::IntKind;
use crate::type_checker::{Kind, Ty};

use std::rc::Rc;

use smol_str::SmolStr;

pub type Id = SmolStr;

/// Things with location information.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct L<T> {
    pub loc: Loc,
    pub node: T,
}

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct Loc {
    /// Module file path, relative to the working directory.
    pub module: Rc<str>,
    pub line_start: u16,
    pub col_start: u16,
    pub byte_offset_start: u32,
    pub line_end: u16,
    pub col_end: u16,
    pub byte_offset_end: u32,
}

impl std::fmt::Debug for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&format!(
            "{}:{}:{}-{}:{}",
            self.module,
            self.line_start + 1,
            self.col_start + 1,
            self.line_end + 1,
            self.col_end + 1,
        ))
    }
}

impl Loc {
    pub fn dummy() -> Self {
        Loc {
            module: "".into(),
            line_start: 0,
            col_start: 0,
            byte_offset_start: 0,
            line_end: 0,
            col_end: 0,
            byte_offset_end: 0,
        }
    }
}

impl<T> L<T> {
    pub fn new(module: &Rc<str>, start: lexgen_util::Loc, end: lexgen_util::Loc, node: T) -> Self {
        L {
            loc: Loc::from_lexgen(module, start, end),
            node,
        }
    }

    pub fn map<T2, F>(self, f: F) -> L<T2>
    where
        F: FnOnce(T) -> T2,
    {
        let L { loc, node } = self;
        L { loc, node: f(node) }
    }

    pub fn map_as_ref<T2, F>(&self, f: F) -> L<T2>
    where
        F: FnOnce(&T) -> T2,
    {
        let L { loc, node } = &self;
        L {
            loc: loc.clone(),
            node: f(node),
        }
    }

    pub fn set_node<T2>(&self, node: T2) -> L<T2> {
        L {
            loc: self.loc.clone(),
            node,
        }
    }
}

impl Loc {
    pub fn from_lexgen(module: &Rc<str>, start: lexgen_util::Loc, end: lexgen_util::Loc) -> Self {
        Loc {
            module: module.clone(),
            line_start: start.line as u16,
            col_start: start.col as u16,
            byte_offset_start: start.byte_idx as u32,
            line_end: end.line as u16,
            col_end: end.col as u16,
            byte_offset_end: end.byte_idx as u32,
        }
    }
}

pub type Module = Vec<L<TopDecl>>;

/// A top-level declaration.
#[derive(Debug, Clone)]
pub enum TopDecl {
    /// A type declaration: `type T = ...`.
    Type(L<TypeDecl>),

    /// A function declaration: `fn f(...) = ...`.
    Fun(L<FunDecl>),

    /// An import declaration.
    Import(L<ImportDecl>),

    /// A trait declaration.
    Trait(L<TraitDecl>),

    /// An `impl` block, implementing a trait or associated methods for a type.
    Impl(L<ImplDecl>),
}

/// A type declaration: `type Vec[t]: ...`.
#[derive(Debug, Clone)]
pub struct TypeDecl {
    /// The type name. `Vec` in the example.
    pub name: Id,

    /// Type parameters of the type. `[t]` in the example.
    pub type_params: Vec<Id>,

    /// Kinds of `type_params`. Filled in by kind inference.
    pub type_param_kinds: Vec<Kind>,

    /// Constructors of the type.
    pub rhs: Option<TypeDeclRhs>,
}

/// Constructors of a type declaration.
#[derive(Debug, Clone)]
pub enum TypeDeclRhs {
    /// A sum type, with more than one constructor.
    Sum(Vec<ConstructorDecl>),

    /// A product type uses the type name as the constructor and only has fields.
    Product(ConstructorFields),
}

/// A sum type constructor.
#[derive(Debug, Clone)]
pub struct ConstructorDecl {
    pub name: Id,
    pub fields: ConstructorFields,
}

#[derive(Debug, Clone)]
pub enum ConstructorFields {
    Empty,
    Named(Vec<(Id, Type)>),
    Unnamed(Vec<Type>),
}

#[derive(Debug, Clone)]
pub enum Type {
    /// A type constructor, potentially applied some number of arguments. E.g. `I32`, `Vec[T]`.
    Named(NamedType),

    /// A type variable.
    ///
    /// We don't have higher-kinded types for now, so type variables cannot be applied.
    Var(Id),

    /// An anonymous record type, e.g. `(x: I32, y: I32)`, `(a: Str, ..R)`.
    Record {
        fields: Vec<Named<Type>>,
        extension: Option<Id>,
        is_row: bool,
    },

    /// An anonymous variant type, e.g. `[Error(msg: Str), Ok, ..R]`.
    Variant {
        alts: Vec<VariantAlt>,
        extension: Option<Id>,
        is_row: bool,
    },

    /// A function type: `Fn(I32): Bool`.
    Fn(FnType),
}

#[derive(Debug, Clone)]
pub struct VariantAlt {
    pub con: Id,
    pub fields: Vec<Named<Type>>,
}

/// A named type, e.g. `I32`, `Vec[I32]`, `Iterator[coll, Str]`.
#[derive(Debug, Clone)]
pub struct NamedType {
    /// Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    pub name: Id,

    /// Arguments of the type constructor.
    pub args: Vec<L<Type>>,
}

#[derive(Debug, Clone)]
pub struct FnType {
    pub args: Vec<L<Type>>,

    /// Optional return type of the function. `()` when omitted.
    pub ret: Option<L<Box<Type>>>,

    /// Same as `FunSig.exceptions`.
    pub exceptions: Option<L<Box<Type>>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Named<T> {
    pub name: Option<Id>,
    pub node: T,
}

impl<T> Named<T> {
    pub fn map_as_ref<T2, F>(&self, f: F) -> Named<T2>
    where
        F: FnOnce(&T) -> T2,
    {
        let Named { name, node } = &self;
        Named {
            name: name.clone(),
            node: f(node),
        }
    }
}

/// Type signature part of a function declaration: type parameters, value parameters, exception
/// type, return type.
#[derive(Debug, Clone)]
pub struct FunSig {
    /// Predicates of the function, e.g. in `id[Debug[t]](a: t)` this is `[Debug[t]]`.
    pub context: Context,

    /// Whether the function has a `self` parameter.
    pub self_: SelfParam,

    /// Parameters of the function.
    ///
    /// Note: this does not include `self`!
    ///
    /// Type is optional for `fn` expressions, where we can sometimes use the type information from
    /// the `fn` use site to give types to arguments.
    pub params: Vec<(Id, Option<L<Type>>)>,

    /// Optional return type.
    ///
    /// When not available in a top-level definition, this defaults to `()`. In a `fn`, we use the
    /// type information at the `fn` use site or fail and ask user to add type annotation.
    pub return_ty: Option<L<Type>>,

    /// The exception signature.
    ///
    /// When not available in a top-level definition, this will be a quantified type variable that
    /// is not used anywhere else in the signature.
    ///
    /// When not available in a `fn` expr, the exception type will be inferred.
    pub exceptions: Option<L<Type>>,
}

#[derive(Debug, Clone)]
pub enum SelfParam {
    No,
    Implicit,
    Explicit(L<Type>),
}

#[derive(Debug, Clone)]

pub struct FunDecl {
    /// Only in associated functions: the parent type. E.g. `Vec` in `Vec.push(...) = ...`.
    pub parent_ty: Option<L<Id>>,

    /// Name of the function.
    pub name: L<Id>,

    /// Type signature of the function.
    pub sig: FunSig,

    /// Body (code) of the function. Not available in `prim` functions.
    pub body: Option<Vec<L<Stmt>>>,
}

impl FunDecl {
    pub fn num_params(&self) -> u32 {
        (match self.sig.self_ {
            SelfParam::No => 0,
            SelfParam::Implicit | SelfParam::Explicit(_) => 1,
        }) + (self.sig.params.len() as u32)
    }
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Let(LetStmt),
    // LetFn(FunDecl),
    Assign(AssignStmt),
    Expr(L<Expr>),
    For(ForStmt),
    While(WhileStmt),
    Break {
        label: Option<Id>,

        /// How many levels of loops to break. Parser initializes this as 0, type checker updates
        /// based on the labels of enclosing loops.
        level: u32,
    },
    Continue {
        label: Option<Id>,

        /// Same as `Break.level`.
        level: u32,
    },
}

/// A let statement: `let x: T = expr`.
#[derive(Debug, Clone)]
pub struct LetStmt {
    pub lhs: L<Pat>,
    pub ty: Option<L<Type>>,
    pub rhs: L<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchExpr {
    pub scrutinee: Box<L<Expr>>,
    pub alts: Vec<Alt>,
}

#[derive(Debug, Clone)]
pub struct Alt {
    pub pattern: L<Pat>,
    pub guard: Option<L<Expr>>,
    pub rhs: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Pat {
    /// Matches anything, binds it to variable.
    Var(VarPat),

    /// Matches a constructor.
    Constr(ConstrPattern),

    /// Matches a variant.
    Variant(VariantPattern),

    Record(RecordPattern),

    /// Underscore, aka. wildcard.
    Ignore,

    /// Matches the string.
    Str(String),

    /// Matches the character.
    Char(char),

    /// Match the prefix, bind the rest. E.g. `"a" .. rest`.
    StrPfx(String, Option<Id>),

    /// Or pattern: `<pat1> | <pat2>`.
    Or(Box<L<Pat>>, Box<L<Pat>>),
}

#[derive(Debug, Clone)]
pub struct VarPat {
    pub var: Id,

    /// Inferred type of the binder. Filled in by the type checker.
    pub ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct ConstrPattern {
    pub constr: Constructor,

    pub fields: Vec<Named<L<Pat>>>,

    /// Whether we ignore fields with `..`: `MyStruct(a = 1u32, ..)`.
    pub ignore_rest: bool,
}

#[derive(Debug, Clone)]
pub struct RecordPattern {
    pub fields: Vec<Named<L<Pat>>>,
    pub ignore_rest: bool,
    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub ty: Id,
    pub constr: Option<Id>,
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct VariantPattern {
    pub constr: Id,
    pub fields: Vec<Named<L<Pat>>>,
}

#[derive(Debug, Clone)]
pub struct IfExpr {
    // At least one element
    pub branches: Vec<(L<Expr>, Vec<L<Stmt>>)>,
    pub else_branch: Option<Vec<L<Stmt>>>,
}

#[derive(Debug, Clone)]
pub struct AssignStmt {
    pub lhs: L<Expr>,
    pub rhs: L<Expr>,
    pub op: AssignOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
    CaretEq,
}

#[derive(Debug, Clone)]
pub struct ForStmt {
    pub label: Option<Id>,

    pub pat: L<Pat>,

    /// Type annotation on the loop variable, the `item` type in `Iterator[iter, item]`.
    pub ast_ty: Option<L<Type>>,

    /// `ast_ty`, converted to type checking types by the type checker.
    pub tc_ty: Option<Ty>,

    pub expr: L<Expr>,

    /// Filled in by the type checker: the iterator type. `iter` in `Iterator[iter, item]`.
    pub expr_ty: Option<Ty>,

    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub label: Option<Id>,
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    /// A variable: `x`.
    Var(VarExpr),

    /// A constructor: `Option.None`, `Result.Ok`, `Bool.True`, `Vec`.
    ConstrSelect(Constructor),

    /// A field selection: `<expr>.x` where `x` is a field.
    ///
    /// Parser generates this node for all expression of form `<expr>.<id>`, type checker converts
    /// method selection expressions to `MethodSelect`.
    FieldSelect(FieldSelectExpr),

    /// A method selection: `<expr>.x` where `x` is a method.
    ///
    /// This node is generated by the type checker.
    MethodSelect(MethodSelectExpr),

    /// An associated function or method selection:
    ///
    /// - Associated function: `Vec.withCapacity`.
    /// - Method: `Vec.push`.
    AssocFnSelect(AssocFnSelectExpr),

    /// A function call: `f(a)`.
    Call(CallExpr),

    /// An integer literal.
    Int(IntExpr),

    /// A string literal.
    String(Vec<StringPart>),

    /// A character literal.
    Char(char),

    Self_,

    /// A binary operator: `x + y`, `i >> 2`.
    ///
    /// Some of the binary operators are desugared to method calls by the type checker.
    BinOp(BinOpExpr),

    /// A unary operator: `-x`, `!b`.
    ///
    /// Some of the unary operators are desugared to method calls by the type checker.
    UnOp(UnOpExpr),

    /// A record: `(1, 2)`, `(x = 123, msg = "hi")`.
    Record(Vec<Named<L<Expr>>>),

    /// A variant: "~A" (nullary), "~ParseError(...)".
    ///
    /// Because "~A" is type checked differently from "~A(1)", we parse variant applications as
    /// `Expr::Variant` instead of `Expr::Call` with a variant as the function.
    Variant(VariantExpr),

    Return(Box<L<Expr>>),

    Match(MatchExpr),

    If(IfExpr),

    Fn(FnExpr),

    Is(IsExpr),

    /// A sequence: `[a, b, c]` or `[a = b, c = d]`. Can be empty.
    Seq(Vec<(Option<L<Expr>>, L<Expr>)>),
}

#[derive(Debug, Clone)]
pub struct VarExpr {
    pub id: Id,

    /// Inferred type arguments of the variable. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct VariantExpr {
    pub id: Id,
    pub args: Vec<Named<L<Expr>>>,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<CallArg>,
}

#[derive(Debug, Clone)]
pub struct CallArg {
    pub name: Option<Id>,
    pub expr: L<Expr>,
}

/// A field selection: `<expr>.x`.
#[derive(Debug, Clone)]
pub struct FieldSelectExpr {
    pub object: Box<L<Expr>>,
    pub field: Id,
}

/// A method selection: `<expr>.method`.
///
/// This node is generated by the type checker, from `Expr::FieldSelect`.
///
/// Methods are always associated functions. They can be associated to a type (e.g. `Vec.push`) or
/// trait methods (e.g. `Iterator.next`).
#[derive(Debug, Clone)]
pub struct MethodSelectExpr {
    /// The reciever, `<expr>` in `<expr>.method`.
    pub object: Box<L<Expr>>,

    /// Type of `object` (receiver), filled in by the type checker.
    ///
    /// This type will always be a type constructor, potentially with arguments, as types without type
    /// constructors (records etc.) don't have methods.
    ///
    /// The type constructor will be the type with the associated function with `method` as the name
    /// and a `self` parameter that matches this type.
    // TODO: We could have separate fields for the ty con and args.
    // TODO: We could also add types to every expression if it's going to help with monomorphisation.
    //       For efficiency though, we should only annotate inferred types and then type check from the
    //       top-level expression every time we need to compute type of an expr.
    pub object_ty: Option<Ty>,

    /// The type or trait id that defines the method.
    ///
    /// E.g. `Vec`, `Iterator`.
    ///
    /// Note: when calling trait methods, this will be the trait type rather than the receiver type.
    pub method_ty_id: Id,

    /// The method id.
    ///
    /// E.g. `push`, `next`.
    pub method: Id,

    /// Type arguments of `method_ty_id`.
    ///
    /// If the method is for a trait, the first arguments here will be for the trait type
    /// parameters. E.g. in `Iterator.next`, the first two argumetns will be the `iter` and `item`
    /// parameters of `trait Iterator[iter, item]`.
    ///
    /// (If the method is not a trait method, then we don't care about the type parameter order.. I
    /// think?)
    pub ty_args: Vec<Ty>,
}

/// An associated function or method selection:
///
/// - Associated function: `Vec.withCapacity`.
/// - Method: `Vec.push`.
#[derive(Debug, Clone)]
pub struct AssocFnSelectExpr {
    pub ty: Id,
    pub member: Id,

    /// Inferred type arguments of the type and assocaited function. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct BinOpExpr {
    pub left: Box<L<Expr>>,
    pub right: Box<L<Expr>>,
    pub op: BinOp,
}

#[derive(Debug, Clone)]
pub struct UnOpExpr {
    pub op: UnOp,
    pub expr: Box<L<Expr>>,
}

#[derive(Debug, Clone)]
pub struct IntExpr {
    /// The digits of the integer, without any prefix ("0x" or "0b") and suffix ("u32" etc.).
    ///
    /// The digits will be parsed during type checking. If the integer doesn't have a suffix,
    /// parsing will be done based on the inferred type of the integer.
    pub text: String,

    /// Suffix of the integer. Initially as parsed. If not available, the type checker updates
    /// this based on the inferred type of the integer.
    pub suffix: Option<IntKind>,

    pub radix: u32,

    /// Filled in by the type checker. The parsed integer.
    ///
    /// This will be the integer value in two's complement, extended to unsiged 64-bit.
    /// E.g. `-1u8` will be `0x00000000000000ff`, instead of `0xffffffffffffffff`.
    pub parsed: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Subtract,
    Equal,
    NotEqual,
    Multiply,
    Divide,
    Lt,
    Gt,
    LtEq,
    GtEq,
    And,
    Or,
    BitAnd,
    BitOr,
    LeftShift,
    RightShift,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone)]
pub struct FnExpr {
    pub sig: FunSig,
    pub body: Vec<L<Stmt>>,
    pub idx: u32,
    pub inferred_ty: Option<Ty>,
}

/// `<expr> is <pat>`: matches expression against pattern.
///
/// Can bind variables.
#[derive(Debug, Clone)]
pub struct IsExpr {
    pub expr: Box<L<Expr>>,
    pub pat: L<Pat>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    /// Import path, e.g. `Fir.Prelude`.
    pub path: Vec<Id>,
    // TODO: Imported thing list, renaming (`as`).
}

#[derive(Debug, Clone)]
pub struct TraitDecl {
    /// Trait name.
    pub name: L<Id>,

    /// Type parameters of the trait.
    pub type_params: Vec<L<Id>>,

    /// Kinds of `type_params`. Filled in by kind inference.
    pub type_param_kinds: Vec<Kind>,

    /// Methods of the trait.
    pub items: Vec<L<FunDecl>>,
}

/// Type parameter and predicates of an `impl` or function.
///
/// E.g. `[Iterator[coll, item], Debug[item]]`.
#[derive(Debug, Clone, Default)]
pub struct Context {
    /// Type parameters, generated by the type checker.
    pub type_params: Vec<(Id, Kind)>,

    /// Predicates.
    pub preds: Vec<L<Type>>,
}

/// An `impl` block, implementing a trait for a type.
///
/// ```ignore
/// impl[ToStr[a]] ToStr[Vec[a]]:
///   toStr(self): Str = ...
///
/// impl Iterator[VecIter[a], a]:
///   next(self): Option[a] = ...
/// ```
#[derive(Debug, Clone)]
pub struct ImplDecl {
    /// Predicates of the `impl` block.
    ///
    /// In the example: `[ToStr[a]]`.
    pub context: Context,

    /// The trait name.
    ///
    /// In the example: `ToStr`.
    pub trait_: L<Id>,

    /// Type parameters of the trait.
    ///
    /// In the example: `[Vec[a]]`.
    pub tys: Vec<L<Type>>,

    /// Method implementations.
    pub items: Vec<L<FunDecl>>,
}

impl Type {
    /// Substitute star-kinded `ty` for `var` in `self`.
    pub fn subst_id(&self, var: &Id, ty: &Type) -> Type {
        self.subst_ids(&[(var.clone(), ty.clone())].into_iter().collect())
    }

    pub fn subst_ids(&self, substs: &Map<Id, Type>) -> Type {
        match self {
            Type::Named(NamedType { name, args }) => Type::Named(NamedType {
                name: match substs.get(name) {
                    Some(ty) => {
                        assert!(args.is_empty());
                        return ty.clone();
                    }
                    None => name.clone(),
                },
                args: args
                    .iter()
                    .map(|L { loc, node: ty_ }| L {
                        loc: loc.clone(),
                        node: ty_.subst_ids(substs),
                    })
                    .collect(),
            }),

            Type::Var(var_) => match substs.get(var_) {
                Some(ty) => ty.clone(),
                None => Type::Var(var_.clone()),
            },

            Type::Record {
                fields,
                extension,
                is_row,
            } => {
                let mut fields: Vec<Named<Type>> = fields
                    .iter()
                    .map(|Named { name, node }| Named {
                        name: name.clone(),
                        node: node.subst_ids(substs),
                    })
                    .collect();

                let mut extension = extension.clone();

                if let Some(ext) = &extension {
                    if let Some(ext_ty) = substs.get(ext) {
                        match ext_ty {
                            Type::Var(new_ext) => extension = Some(new_ext.clone()),

                            Type::Record {
                                fields: ext_fields,
                                extension: new_ext,
                                is_row,
                            } => {
                                assert!(*is_row);
                                fields.extend(ext_fields.iter().cloned());
                                extension = new_ext.clone();
                            }

                            _ => panic!(
                                "Weird substitution for record extension {}: {}",
                                ext, ext_ty
                            ),
                        }
                    };
                }

                Type::Record {
                    fields,
                    extension,
                    is_row: *is_row,
                }
            }

            Type::Variant {
                alts,
                extension,
                is_row,
            } => {
                let mut alts: Vec<VariantAlt> = alts
                    .iter()
                    .map(|VariantAlt { con, fields }| VariantAlt {
                        con: con.clone(),
                        fields: fields
                            .iter()
                            .map(|Named { name, node }| Named {
                                name: name.clone(),
                                node: node.subst_ids(substs),
                            })
                            .collect(),
                    })
                    .collect();

                let mut extension = extension.clone();

                if let Some(ext) = &extension {
                    if let Some(ext_ty) = substs.get(ext) {
                        match ext_ty {
                            Type::Var(new_ext) => extension = Some(new_ext.clone()),

                            Type::Variant {
                                alts: ext_alts,
                                extension: new_ext,
                                is_row,
                            } => {
                                assert!(*is_row);
                                alts.extend(ext_alts.iter().cloned());
                                extension = new_ext.clone();
                            }

                            _ => panic!(
                                "Weird substitution for variant extension {}: {}",
                                ext, ext_ty
                            ),
                        }
                    }
                }

                Type::Variant {
                    alts,
                    extension,
                    is_row: *is_row,
                }
            }

            Type::Fn(FnType {
                args,
                ret,
                exceptions,
            }) => Type::Fn(FnType {
                args: args
                    .iter()
                    .map(|arg| arg.map_as_ref(|arg| arg.subst_ids(substs)))
                    .collect(),
                ret: ret
                    .as_ref()
                    .map(|ret| ret.map_as_ref(|ret| Box::new(ret.subst_ids(substs)))),
                exceptions: exceptions
                    .as_ref()
                    .map(|exn| exn.map_as_ref(|exn| Box::new(exn.subst_ids(substs)))),
            }),
        }
    }

    pub fn as_named_type(&self) -> &NamedType {
        match self {
            Type::Named(named_type) => named_type,
            _ => panic!(),
        }
    }
}

impl Stmt {
    pub fn subst_ty_ids(&mut self, substs: &Map<Id, Type>) {
        match self {
            Stmt::Let(LetStmt { lhs: _, ty, rhs }) => {
                if let Some(ty) = ty {
                    ty.node = ty.node.subst_ids(substs);
                }
                rhs.node.subst_ty_ids(substs);
            }

            Stmt::Assign(AssignStmt { lhs, rhs, op: _ }) => {
                lhs.node.subst_ty_ids(substs);
                rhs.node.subst_ty_ids(substs);
            }

            Stmt::Expr(expr) => expr.node.subst_ty_ids(substs),

            Stmt::For(ForStmt {
                label: _,
                pat: _,
                ast_ty,
                tc_ty: _,
                expr,
                expr_ty: _,
                body,
            }) => {
                if let Some(ast_ty) = ast_ty {
                    ast_ty.node = ast_ty.node.subst_ids(substs);
                }
                expr.node.subst_ty_ids(substs);
                for stmt in body {
                    stmt.node.subst_ty_ids(substs);
                }
            }

            Stmt::While(WhileStmt {
                label: _,
                cond,
                body,
            }) => {
                cond.node.subst_ty_ids(substs);
                for stmt in body {
                    stmt.node.subst_ty_ids(substs);
                }
            }

            Stmt::Break { label: _, level: _ } => {}

            Stmt::Continue { label: _, level: _ } => {}
        }
    }
}

impl Expr {
    pub fn subst_ty_ids(&mut self, substs: &Map<Id, Type>) {
        match self {
            Expr::Var(_)
            | Expr::ConstrSelect(_)
            | Expr::AssocFnSelect(_)
            | Expr::Int(_)
            | Expr::Char(_)
            | Expr::Self_ => {}

            Expr::FieldSelect(FieldSelectExpr { object, field: _ }) => {
                object.node.subst_ty_ids(substs);
            }

            Expr::MethodSelect(MethodSelectExpr {
                object,
                object_ty: _,
                method_ty_id: _,
                method: _,
                ty_args: _,
            }) => {
                object.node.subst_ty_ids(substs);
            }

            Expr::Call(CallExpr { fun, args }) => {
                fun.node.subst_ty_ids(substs);
                for CallArg { name: _, expr } in args {
                    expr.node.subst_ty_ids(substs);
                }
            }

            Expr::String(parts) => {
                for part in parts {
                    match part {
                        StringPart::Str(_) => {}
                        StringPart::Expr(expr) => expr.node.subst_ty_ids(substs),
                    }
                }
            }

            Expr::BinOp(BinOpExpr { left, right, op: _ }) => {
                left.node.subst_ty_ids(substs);
                right.node.subst_ty_ids(substs);
            }

            Expr::UnOp(UnOpExpr { op: _, expr }) => {
                expr.node.subst_ty_ids(substs);
            }

            Expr::Record(fields) => {
                for field in fields {
                    field.node.node.subst_ty_ids(substs);
                }
            }

            Expr::Variant(VariantExpr { id: _, args }) => {
                for field in args {
                    field.node.node.subst_ty_ids(substs);
                }
            }

            Expr::Return(expr) => expr.node.subst_ty_ids(substs),

            Expr::Match(MatchExpr { scrutinee, alts }) => {
                scrutinee.node.subst_ty_ids(substs);
                for Alt {
                    pattern: _,
                    guard,
                    rhs,
                } in alts
                {
                    if let Some(guard) = guard {
                        guard.node.subst_ty_ids(substs);
                    }
                    for stmt in rhs {
                        stmt.node.subst_ty_ids(substs);
                    }
                }
            }

            Expr::If(IfExpr {
                branches,
                else_branch,
            }) => {
                for (lhs, rhs) in branches {
                    lhs.node.subst_ty_ids(substs);
                    for stmt in rhs {
                        stmt.node.subst_ty_ids(substs);
                    }
                }
                if let Some(else_branch) = else_branch {
                    for stmt in else_branch {
                        stmt.node.subst_ty_ids(substs);
                    }
                }
            }

            Expr::Fn(FnExpr {
                sig,
                body,
                idx: _,
                inferred_ty: _,
            }) => {
                sig.subst_ty_ids(substs);
                for stmt in body {
                    stmt.node.subst_ty_ids(substs);
                }
            }

            Expr::Is(IsExpr { expr, pat: _ }) => {
                expr.node.subst_ty_ids(substs);
            }

            Expr::Seq(elems) => {
                for (k, v) in elems {
                    if let Some(k) = k {
                        k.node.subst_ty_ids(substs);
                    }
                    v.node.subst_ty_ids(substs);
                }
            }
        }
    }
}

impl FunSig {
    pub fn subst_ty_ids(&mut self, substs: &Map<Id, Type>) {
        match &mut self.self_ {
            SelfParam::No => {}
            SelfParam::Implicit => {
                // Traits methods can't have implicit `self` type, checked in the previous pass
                // in this function (`collect_cons`).
                panic!()
            }
            SelfParam::Explicit(ty) => {
                ty.node = ty.node.subst_ids(substs);
            }
        }

        for (_, param_ty) in &mut self.params {
            if let Some(param_ty) = param_ty {
                param_ty.node = param_ty.node.subst_ids(substs);
            }
        }

        if let Some(return_ty) = &mut self.return_ty {
            return_ty.node = return_ty.node.subst_ids(substs);
        }

        if let Some(exceptions) = &mut self.exceptions {
            exceptions.node = exceptions.node.subst_ids(substs);
        }
    }
}
