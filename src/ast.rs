#![allow(clippy::enum_variant_names)]

pub mod printer;

use crate::collections::Map;
use crate::interpolation::StringPart;
pub use crate::token::IntKind;
use crate::type_checker::Ty;

use std::rc::Rc;

use smol_str::SmolStr;

pub type ParsedId = SmolStr;

pub type ParsedModule = Module<ParsedId>;
pub type ParsedTopDecl = TopDecl<ParsedId>;
pub type ParsedTypeDecl = TypeDecl<ParsedId>;
pub type ParsedTypeDeclRhs = TypeDeclRhs<ParsedId>;
pub type ParsedConstructorDecl = ConstructorDecl<ParsedId>;
pub type ParsedConstructorFields = ConstructorFields<ParsedId>;
pub type ParsedType = Type<ParsedId>;
pub type ParsedVariantAlt = VariantAlt<ParsedId>;
pub type ParsedNamedType = NamedType<ParsedId>;
pub type ParsedFnType = FnType<ParsedId>;
pub type ParsedNamed<T> = Named<T, ParsedId>;
pub type ParsedFunSig = FunSig<ParsedId>;
pub type ParsedFunDecl = FunDecl<ParsedId>;
pub type ParsedStmt = Stmt<ParsedId>;
pub type ParsedLetStmt = LetStmt<ParsedId>;
pub type ParsedMatchExpr = MatchExpr<ParsedId>;
pub type ParsedAlt = Alt<ParsedId>;
pub type ParsedPat = Pat<ParsedId>;
pub type ParsedConstrPattern = ConstrPattern<ParsedId>;
pub type ParsedConstructor = Constructor<ParsedId>;
pub type ParsedVariantPattern = VariantPattern<ParsedId>;
pub type ParsedIfExpr = IfExpr<ParsedId>;
pub type ParsedAssignStmt = AssignStmt<ParsedId>;
pub type ParsedForStmt = ForStmt<ParsedId>;
pub type ParsedWhileStmt = WhileStmt<ParsedId>;
pub type ParsedWhileLetStmt = WhileLetStmt<ParsedId>;
pub type ParsedExpr = Expr<ParsedId>;
pub type ParsedVarExpr = VarExpr<ParsedId>;
pub type ParsedConstrExpr = ConstrExpr<ParsedId>;
pub type ParsedVariantExpr = VariantExpr<ParsedId>;
pub type ParsedCallExpr = CallExpr<ParsedId>;
pub type ParsedCallArg = CallArg<ParsedId>;
pub type ParsedFieldSelectExpr = FieldSelectExpr<ParsedId>;
pub type ParsedMethodSelectExpr = MethodSelectExpr<ParsedId>;
pub type ParsedConstrSelectExpr = ConstrSelectExpr<ParsedId>;
pub type ParsedAssocFnSelectExpr = AssocFnSelectExpr<ParsedId>;
pub type ParsedBinOpExpr = BinOpExpr<ParsedId>;
pub type ParsedUnOpExpr = UnOpExpr<ParsedId>;
pub type ParsedFnExpr = FnExpr<ParsedId>;
pub type ParsedImportDecl = ImportDecl<ParsedId>;
pub type ParsedTraitDecl = TraitDecl<ParsedId>;
pub type ParsedTraitDeclItem = TraitDeclItem<ParsedId>;
pub type ParsedContext = Context<ParsedId>;
pub type ParsedTypeParam = TypeParam<ParsedId>;
pub type ParsedImplDecl = ImplDecl<ParsedId>;
pub type ParsedImplDeclItem = ImplDeclItem<ParsedId>;
pub type ParsedAssocTyDecl = AssocTyDecl<ParsedId>;

/// Things with location information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct L<T> {
    pub loc: Loc,
    pub node: T,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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

pub type Module<Id> = Vec<L<TopDecl<Id>>>;

/// A top-level declaration.
#[derive(Debug, Clone)]
pub enum TopDecl<Id> {
    /// A type declaration: `type T = ...`.
    Type(L<TypeDecl<Id>>),

    /// A function declaration: `fn f(...) = ...`.
    Fun(L<FunDecl<Id>>),

    /// An import declaration.
    Import(L<ImportDecl<Id>>),

    /// A trait declaration.
    Trait(L<TraitDecl<Id>>),

    /// An `impl` block, implementing a trait or associated methods for a type.
    Impl(L<ImplDecl<Id>>),
}

/// A type declaration: `type Vec[T] = ...`.
#[derive(Debug, Clone)]
pub struct TypeDecl<Id> {
    /// The type name, e.g. `Vec`.
    pub name: Id,

    /// Type parameters, e.g. `[T]`.
    pub type_params: Vec<Id>,

    /// Constructors of the type.
    pub rhs: Option<TypeDeclRhs<Id>>,
}

/// Constructors of a type declaration.
#[derive(Debug, Clone)]
pub enum TypeDeclRhs<Id> {
    /// A sum type, with more than one constructor.
    Sum(Vec<ConstructorDecl<Id>>),

    /// A product type uses the type name as the constructor and only has fields.
    Product(ConstructorFields<Id>),
}

/// A sum type constructor.
#[derive(Debug, Clone)]
pub struct ConstructorDecl<Id> {
    pub name: Id,
    pub fields: ConstructorFields<Id>,
}

#[derive(Debug, Clone)]
pub enum ConstructorFields<Id> {
    Empty,
    Named(Vec<(Id, Type<Id>)>),
    Unnamed(Vec<Type<Id>>),
}

#[derive(Debug, Clone)]
pub enum Type<Id> {
    /// A type constructor, potentially applied some number of arguments. E.g. `I32`, `Vec[T]`.
    Named(NamedType<Id>),

    /// A type variable.
    ///
    /// We don't have higher-kinded types for now, so type variables cannot be applied.
    Var(Id),

    /// An anonymous record type, e.g. `(x: I32, y: I32)`, `(a: Str, ..R)`.
    Record {
        fields: Vec<Named<Type<Id>, Id>>,
        extension: Option<Id>,
    },

    /// An anonymous variant type, e.g. `[Error(msg: Str), Ok, ..R]`.
    Variant {
        alts: Vec<VariantAlt<Id>>,
        extension: Option<Id>,
    },

    /// A function type: `Fn(I32): Bool`.
    Fn(FnType<Id>),
}

#[derive(Debug, Clone)]
pub struct VariantAlt<Id> {
    pub con: Id,
    pub fields: Vec<Named<Type<Id>, Id>>,
}

/// A named type, e.g. `I32`, `Vec[I32]`, `Iterator[Item = A]`.
#[derive(Debug, Clone)]
pub struct NamedType<Id> {
    /// Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    pub name: Id,

    /// Arguments and associated types of the tyep constructor. Examples:
    ///
    /// - In `I32`, `[]`.
    /// - In `Vec[I32]`, `[(None, I32)]`.
    /// - In `Iterator[Item = A]`, `[(Some(Item), A)]`.
    pub args: Vec<L<(Option<Id>, L<Type<Id>>)>>,
}

#[derive(Debug, Clone)]
pub struct FnType<Id> {
    pub args: Vec<L<Type<Id>>>,

    pub ret: Option<L<Box<Type<Id>>>>,

    /// Same as `FunSig.exceptions`.
    pub exceptions: Option<L<Box<Type<Id>>>>,
}

#[derive(Debug, Clone)]
pub struct Named<T, Id> {
    pub name: Option<Id>,
    pub node: T,
}

impl<T, Id: Clone> Named<T, Id> {
    pub fn map_as_ref<T2, F>(&self, f: F) -> Named<T2, Id>
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
pub struct FunSig<Id> {
    /// Type parameters of the function, e.g. in `fn id[T: Debug](a: T)` this is `[T: Debug]`.
    ///
    /// The bound can refer to assocaited types, e.g. `[A, I: Iterator[Item = A]]`.
    pub type_params: Context<Id>,

    /// Whether the function has a `self` parameter.
    pub self_: bool,

    /// Parameters of the function.
    pub params: Vec<(Id, L<Type<Id>>)>,

    /// Optional return type.
    pub return_ty: Option<L<Type<Id>>>,

    /// The exception signature. If exists, this will be a variant type. Store as `Type` to make it
    /// easier to process with rest of the types.
    pub exceptions: Option<L<Type<Id>>>,
}

#[derive(Debug, Clone)]
pub struct FunDecl<Id> {
    pub name: L<Id>,
    pub sig: FunSig<Id>,
    pub body: Option<Vec<L<Stmt<Id>>>>,
}

impl<Id> FunDecl<Id> {
    pub fn num_params(&self) -> u32 {
        self.sig.params.len() as u32 + if self.sig.self_ { 1 } else { 0 }
    }
}

#[derive(Debug, Clone)]
pub enum Stmt<Id> {
    Let(LetStmt<Id>),
    // LetFn(FunDecl),
    Assign(AssignStmt<Id>),
    Expr(L<Expr<Id>>),
    For(ForStmt<Id>),
    While(WhileStmt<Id>),
    WhileLet(WhileLetStmt<Id>),
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
pub struct LetStmt<Id> {
    pub lhs: L<Pat<Id>>,
    pub ty: Option<L<Type<Id>>>,
    pub rhs: L<Expr<Id>>,
}

#[derive(Debug, Clone)]
pub struct MatchExpr<Id> {
    pub scrutinee: Box<L<Expr<Id>>>,
    pub alts: Vec<Alt<Id>>,
}

#[derive(Debug, Clone)]
pub struct Alt<Id> {
    pub pattern: L<Pat<Id>>,
    pub guard: Option<L<Expr<Id>>>,
    pub rhs: Vec<L<Stmt<Id>>>,
}

#[derive(Debug, Clone)]
pub enum Pat<Id> {
    /// Matches anything, binds it to variable.
    Var(Id),

    /// Matches a constructor.
    Constr(ConstrPattern<Id>),

    /// Matches a variant.
    Variant(VariantPattern<Id>),

    Record(Vec<Named<L<Pat<Id>>, Id>>),

    /// Underscore, aka. wildcard.
    Ignore,

    /// Matches the string.
    Str(String),

    /// Matches the character.
    Char(char),

    /// Match the prefix, bind the rest. E.g. `"a" .. rest`.
    StrPfx(String, Id),

    /// Or pattern: `<pat1> | <pat2>`.
    Or(Box<L<Pat<Id>>>, Box<L<Pat<Id>>>),
}

#[derive(Debug, Clone)]
pub struct ConstrPattern<Id> {
    pub constr: Constructor<Id>,
    pub fields: Vec<Named<L<Pat<Id>>, Id>>,

    /// Inferred type arguments of the constructor. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct Constructor<Id> {
    pub type_: Id,
    pub constr: Option<Id>,
}

#[derive(Debug, Clone)]
pub struct VariantPattern<Id> {
    pub constr: Id,
    pub fields: Vec<Named<L<Pat<Id>>, Id>>,
}

#[derive(Debug, Clone)]
pub struct IfExpr<Id> {
    // At least one element
    pub branches: Vec<(L<Expr<Id>>, Vec<L<Stmt<Id>>>)>,
    pub else_branch: Option<Vec<L<Stmt<Id>>>>,
}

#[derive(Debug, Clone)]
pub struct AssignStmt<Id> {
    pub lhs: L<Expr<Id>>,
    pub rhs: L<Expr<Id>>,
    pub op: AssignOp,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssignOp {
    Eq,
    PlusEq,
    MinusEq,
    StarEq,
}

#[derive(Debug, Clone)]
pub struct ForStmt<Id> {
    pub label: Option<Id>,
    pub pat: L<Pat<Id>>,
    pub ty: Option<Type<Id>>,
    pub expr: L<Expr<Id>>,
    pub expr_ty: Option<Ty>, // filled in by the type checker
    pub body: Vec<L<Stmt<Id>>>,
}

#[derive(Debug, Clone)]
pub struct WhileStmt<Id> {
    pub label: Option<Id>,
    pub cond: L<Expr<Id>>,
    pub body: Vec<L<Stmt<Id>>>,
}

#[derive(Debug, Clone)]
pub struct WhileLetStmt<Id> {
    pub label: Option<Id>,
    pub pat: L<Pat<Id>>,
    pub cond: L<Expr<Id>>,
    pub body: Vec<L<Stmt<Id>>>,
}

#[derive(Debug, Clone)]
pub enum Expr<Id> {
    /// A variable: `x`.
    Var(VarExpr<Id>),

    /// A constructor: `Vec`, `Bool`, `I32`.
    Constr(ConstrExpr<Id>),

    /// A variant application: "`A()", "`ParseError(...)".
    ///
    /// Because "`A" is type checked differently from "`A(1)", we parse variant applications as
    /// `Expr::Variant` instead of `Expr::Call` with a variant as the function.
    Variant(VariantExpr<Id>),

    /// A field selection: `<expr>.x` where `x` is a field.
    ///
    /// Parser generates this node for all expression of form `<expr>.<id>`, type checker converts
    /// method selection expressions to `MethodSelect`.
    FieldSelect(FieldSelectExpr<Id>),

    /// A method selection: `<expr>.x` where `x` is a method.
    ///
    /// This node is generated by the type checker.
    MethodSelect(MethodSelectExpr<Id>),

    /// A constructor selection: `Option.None`.
    ConstrSelect(ConstrSelectExpr<Id>),

    /// An associated function or method selection:
    ///
    /// - Associated function: `Vec.withCapacity`.
    /// - Method: `Vec.push`.
    AssocFnSelect(AssocFnSelectExpr<Id>),

    /// A function call: `f(a)`.
    Call(CallExpr<Id>),

    Int(IntExpr),

    String(Vec<StringPart>),

    Char(char),

    Self_,

    BinOp(BinOpExpr<Id>),

    UnOp(UnOpExpr<Id>),

    Record(Vec<Named<L<Expr<Id>>, Id>>),

    Return(Box<L<Expr<Id>>>),

    Match(MatchExpr<Id>),

    If(IfExpr<Id>),

    Fn(FnExpr<Id>),
}

#[derive(Debug, Clone)]
pub struct VarExpr<Id> {
    pub id: Id,

    /// Inferred type arguments of the variable. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct ConstrExpr<Id> {
    pub id: Id,

    /// Inferred type arguments of the constructor. Filled by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct VariantExpr<Id> {
    pub id: Id,
    pub args: Vec<Named<L<Expr<Id>>, Id>>,
}

#[derive(Debug, Clone)]
pub struct CallExpr<Id> {
    pub fun: Box<L<Expr<Id>>>,
    pub args: Vec<CallArg<Id>>,
}

#[derive(Debug, Clone)]
pub struct CallArg<Id> {
    pub name: Option<Id>,
    pub expr: L<Expr<Id>>,
}

/// A field selection: `<expr>.x`.
#[derive(Debug, Clone)]
pub struct FieldSelectExpr<Id> {
    pub object: Box<L<Expr<Id>>>,
    pub field: Id,
}

/// A method selection: `<expr>.x`.
#[derive(Debug, Clone)]
pub struct MethodSelectExpr<Id> {
    pub object: Box<L<Expr<Id>>>,

    /// Type of `object`, filled in by the type checker.
    pub object_ty: Option<Ty>,

    pub method: Id,

    /// Type arguments of the method, filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

/// A constructor selection: `Option.None`.
#[derive(Debug, Clone)]
pub struct ConstrSelectExpr<Id> {
    pub ty: Id,
    pub constr: Id,

    /// Inferred type arguments of the constructor. Filled by the type checker.
    pub ty_args: Vec<Ty>,
}

/// An associated function or method selection:
///
/// - Associated function: `Vec.withCapacity`.
/// - Method: `Vec.push`.
#[derive(Debug, Clone)]
pub struct AssocFnSelectExpr<Id> {
    pub ty: Id,
    pub member: Id,

    /// Inferred type arguments of the type and assocaited function. Filled in by the type checker.
    pub ty_args: Vec<Ty>,
}

#[derive(Debug, Clone)]
pub struct BinOpExpr<Id> {
    pub left: Box<L<Expr<Id>>>,
    pub right: Box<L<Expr<Id>>>,
    pub op: BinOp,
}

#[derive(Debug, Clone)]
pub struct UnOpExpr<Id> {
    pub op: UnOp,
    pub expr: Box<L<Expr<Id>>>,
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
    /// This should be the integer value as expected by the interpreter. E.g. `-1u64` should be
    /// `0x00000000000000ff`, instead of `0xffffffffffffffff`.
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
pub struct FnExpr<Id> {
    pub sig: FunSig<Id>,
    pub body: Vec<L<Stmt<Id>>>,
    pub idx: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl<Id> {
    /// Import path, e.g. `Fir.Prelude`.
    pub path: Vec<Id>,
    // TODO: Imported thing list, renaming (`as`).
}

#[derive(Debug, Clone)]
pub struct TraitDecl<Id> {
    /// Trait name.
    pub name: L<Id>,

    /// Type parameter of the trait, with bounds.
    pub ty: TypeParam<Id>,

    pub items: Vec<L<TraitDeclItem<Id>>>,
}

#[derive(Debug, Clone)]
pub enum TraitDeclItem<Id> {
    /// An associated type, e.g. `type Item`.
    AssocTy(Id),

    /// A method, potentially with a body (default implementation).
    Fun(FunDecl<Id>),
}

/// Type parameters of a function or `impl` block.
///
/// E.g. `[A, I: Iterator[Item = A]]` is represented as `[(A, []), (I, [Item = A])]`.
pub type Context<Id> = Vec<TypeParam<Id>>;

/// A type parameter in a function, `impl`, or `trait` block.
///
/// Example: `I: Iterator[Item = A] + Debug`.
#[derive(Debug, Clone)]
pub struct TypeParam<Id> {
    /// `I` in the example.
    pub id: L<Id>,

    /// `[Iterator[Item = A], Debug]` in the example.
    ///
    /// Reminder: associated types are parsed as named arguments.
    pub bounds: Vec<L<Type<Id>>>,
}

/// An `impl` block, implementing associated functions or methods for a type, or a trait. Examples:
///
/// ```ignore
/// impl[A] Vec[A]:
///     # An associated function.
///     fn withCapacity(cap: U32): Vec[A] = ...
///
///     # A method.
///     fn push(self, elem: A) = ...
///
/// impl[A: ToStr] ToStr for Vec[A]:
///   fn toStr(self): Str = ...
/// ```
#[derive(Debug, Clone)]
pub struct ImplDecl<Id> {
    /// Type parameters of the type being implemented, with bounds.
    ///
    /// In the first example, this is `[A]`. In the second example: `[A: ToStr]`.
    pub context: Context<Id>,

    /// If the `impl` block is for a trait, the trait name.
    ///
    /// In the first example this is `None`. In the second this is `Some(ToStr)`.
    pub trait_: Option<L<Id>>,

    /// The implementing type.
    ///
    /// In both of the examples this is `Vec[A]`.
    pub ty: L<Type<Id>>,

    /// Functions, methods, and associated types.
    pub items: Vec<L<ImplDeclItem<Id>>>,
}

#[derive(Debug, Clone)]
pub enum ImplDeclItem<Id> {
    /// An associated type definition, e.g. `type Item = T`.
    AssocTy(AssocTyDecl<Id>),

    /// A function definition.
    Fun(FunDecl<Id>),
}

#[derive(Debug, Clone)]
pub struct AssocTyDecl<Id> {
    pub name: Id,
    pub ty: L<Type<Id>>,
}

impl<Id: Clone + std::hash::Hash + Eq> Type<Id> {
    /// Substitute star-kinded `ty` for `var` in `self`.
    pub fn subst_id(&self, var: &Id, ty: &Type<Id>) -> Type<Id> {
        self.subst_ids(&[(var.clone(), ty.clone())].into_iter().collect())
    }

    pub fn subst_ids(&self, substs: &Map<Id, Type<Id>>) -> Type<Id> {
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
                    .map(
                        |L {
                             loc,
                             node: (name, ty_),
                         }| L {
                            loc: loc.clone(),
                            node: (name.clone(), ty_.map_as_ref(|ty__| ty__.subst_ids(substs))),
                        },
                    )
                    .collect(),
            }),

            Type::Var(var_) => match substs.get(var_) {
                Some(ty) => ty.clone(),
                None => Type::Var(var_.clone()),
            },

            Type::Record { fields, extension } => Type::Record {
                fields: fields
                    .iter()
                    .map(|Named { name, node }| Named {
                        name: name.clone(),
                        node: node.subst_ids(substs),
                    })
                    .collect(),
                // NB. This does not substitute row types.
                extension: extension.clone(),
            },

            Type::Variant { alts, extension } => Type::Variant {
                alts: alts
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
                    .collect(),
                // NB. This does not substitute row types.
                extension: extension.clone(),
            },

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

    pub fn as_named_type(&self) -> &NamedType<Id> {
        match self {
            Type::Named(named_type) => named_type,
            _ => panic!(),
        }
    }
}
