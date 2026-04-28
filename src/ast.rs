#![allow(clippy::enum_variant_names)]

pub mod printer;

use crate::collections::HashMap;
use crate::interpolation::StrPart;
use crate::module::ModulePath;
pub use crate::name::Name;
pub use crate::token::IntKind;
use crate::type_checker::id::builtins as builtin_ids;
use crate::type_checker::{Id, Kind, Ty};

use std::rc::Rc;

use smol_str::SmolStr;

/// Things with location information.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

    pub fn new_dummy(node: T) -> Self {
        L {
            loc: Loc::dummy(),
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

#[derive(Debug, Clone)]
pub struct Module {
    pub decls: Vec<L<TopDecl>>,
}

impl Module {
    pub fn empty() -> Module {
        Module { decls: vec![] }
    }
}

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

/// A type declaration: `type Vec[t](...)`, `value type Bool: ...`.
#[derive(Debug, Clone)]
pub struct TypeDecl {
    /// Attributes of the type. E.g. `#[derive(ToDoc, Eq)]`.
    pub attr: Option<Attribute>,

    /// Whether this is a value type.
    pub value: bool,

    /// The type name. `Vec` in the example.
    pub name: Name,

    /// Type parameters of the type. `[t]` in the example.
    pub type_params: Vec<TypeParam>,

    /// Kinds of `type_params`. Filled in by kind inference.
    pub type_param_kinds: Vec<Kind>,

    /// Constructors of the type.
    pub rhs: Option<TypeDeclRhs>,
}

/// A type parameter in a type or trait declaration.
///
/// ```ignore
/// trait Foo[r: Row[Rec]]: ...
/// type Bar[x, y: Row[Var]]: ...
/// ```
#[derive(Debug, Clone)]
pub struct TypeParam {
    /// Name of the type parameter. `r`, `x`, `y` in the example.
    pub name: L<Name>,

    /// Optional kind of the type parameter. `Row[Rec]` for `r` in the example. `x` doesn't have a
    /// kind annotation.
    pub kind: Option<L<Type>>,
}

/// Constructors of a type declaration.
#[derive(Debug, Clone)]
pub enum TypeDeclRhs {
    /// A sum type, with more than one constructor.
    Sum {
        cons: Vec<ConDecl>,
        extension: Option<Box<L<Type>>>,
    },

    /// A product type uses the type name as the constructor and only has fields.
    Product(ConFields),

    /// A type synonym: `type Foo = U32`.
    Synonym(L<Type>),
}

/// A sum type constructor.
#[derive(Debug, Clone)]
pub struct ConDecl {
    pub name: Name,
    pub fields: ConFields,
}

#[derive(Debug, Clone)]
pub enum ConFields {
    Empty,
    Named {
        fields: Vec<(Name, L<Type>)>,
        extension: Option<Box<L<Type>>>,
    },
    Unnamed {
        fields: Vec<L<Type>>,
    },
}

#[derive(Debug, Clone)]
pub enum Type {
    /// A type constructor, potentially applied some number of arguments. E.g. `I32`, `Vec[a]`.
    Named(NamedType),

    /// A type variable.
    ///
    /// We don't have higher-kinded types for now, so type variables cannot be applied.
    Var(Name),

    /// An anonymous record type, e.g. `(x: I32, y: I32)`, `(a: Str, ..r)`.
    Record {
        fields: Vec<(Name, L<Type>)>,
        extension: Option<Box<L<Type>>>,
        is_row: bool,
    },

    /// An anonymous variant type, e.g. `[Str, Option[U32], ..r]`.
    Variant {
        alts: Vec<NamedType>,
        extension: Option<Box<L<Type>>>,
        is_row: bool,
    },

    /// A function type: `Fn(I32) Bool / exn`.
    Fn(FnType),

    /// An associated type selection: `Iterator[iter, exn].Item`.
    AssocTySelect { ty: L<Box<Type>>, assoc_ty: Name },
}

/// A named type, e.g. `I32`, `Vec[I32]`, `Iterator[coll, Str]`.
#[derive(Debug, Clone)]
pub struct NamedType {
    /// Module prefix of the type constructor, e.g. in `Fir/Vec/Vec` this is the `Fir/Vec/` part.
    pub mod_prefix: Option<ModulePath>,

    /// Name of the type constructor, e.g. `I32`, `Vec`, `Iterator`.
    pub name: Name,

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
    pub name: Option<Name>,
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

    pub fn set_node<T2>(&self, node: T2) -> Named<T2> {
        Named {
            name: self.name.clone(),
            node,
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
    pub params: Vec<(Name, Option<L<Type>>)>,

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
    pub parent_ty: Option<L<Name>>,

    /// Name of the function.
    pub name: L<Name>,

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
    Assign(AssignStmt),
    Expr(Expr),
    For(ForStmt),
    While(WhileStmt),
    Break {
        label: Option<Name>,

        /// How many levels of loops to break. Parser initializes this as 0, type checker updates
        /// based on the labels of enclosing loops.
        level: u32,
    },
    Continue {
        label: Option<Name>,

        /// Same as `Break.level`.
        level: u32,
    },
}

/// A let statement: `let <pat>: <type> = <expr>`.
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
    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct Alt {
    pub pat: L<Pat>,
    pub guard: Option<L<Expr>>,
    pub rhs: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Pat {
    /// Matches anything, binds it to variable.
    Var(VarPat),

    /// Matches a constructor.
    Con(ConPat),

    /// Underscore, aka. wildcard.
    Ignore,

    /// Matches the string.
    Str(String),

    /// Matches the character.
    Char(char),

    /// Or pattern: `<pat1> | <pat2>`.
    Or(Box<L<Pat>>, Box<L<Pat>>),

    /// A record pattern: `(x, y)` (short for `(x = x, y, = y)`), `(x = <pat1>, y = <pat2>, ...)`.
    Record(RecordPat),

    /// A variant pattern: `~"Hi"`, `~Option.Some(123)`.
    Variant(VariantPat),
}

#[derive(Debug, Clone)]
pub struct VarPat {
    pub var: Name,

    /// Inferred type of the binder. Filled in by the type checker.
    pub ty: Option<Ty>,

    /// Only after type checking: when the binder type is refined by pattern matching, this holds
    /// the refined type.
    pub refined: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct ConPat {
    pub con: Con,

    pub fields: Vec<Named<L<Pat>>>,

    /// Matches the rest of the fields:
    /// - `MyStruct(a = 1u32, ..)` ignores the rest of the fields.
    /// - `MyStruct(a = 1u32, ..rest)` binds `rest` to the rest of the fields as a record.
    pub rest: RestPat,
}

#[derive(Debug, Clone)]
pub struct RecordPat {
    pub fields: Vec<Named<L<Pat>>>,

    /// Matches the rest of the fields:
    /// - `MyStruct(a = 1u32, ..)` ignores the rest of the fields.
    /// - `MyStruct(a = 1u32, ..rest)` binds `rest` to the rest of the fields as a record.
    pub rest: RestPat,

    pub inferred_ty: Option<Ty>,
}

/// An `..` or `..binder` in a record or constructor field.
#[derive(Debug, Clone)]
pub enum RestPat {
    Ignore,
    Bind(VarPat),
    No,
}

#[derive(Debug, Clone)]
pub struct VariantPat {
    pub pat: Box<L<Pat>>,
    pub inferred_ty: Option<Ty>,
    pub inferred_pat_ty: Option<Ty>,
}

/// A product or sum constructor. Examples:
///
/// - `Vec`
/// - `Vec[U32]`
/// - `Option.Some`
/// - `Option[U32].Some`
/// - `Option.Some[U32]`
/// - `Option[t1].Some[t2]`
///
/// Note that the last one is parsed but it will be rejected by the type checker as the two type
/// arguments pass the same type parameters.
///
/// All variants above can get a module prefix:
///
/// - `Prelude/Vec`
/// - `Prelude/Option[U32].Some`
/// - ...
#[derive(Debug, Clone)]
pub struct Con {
    pub mod_prefix: Option<ModulePath>,

    /// Name of the type: `Option`, `Vec`.
    pub ty: Name,

    /// Constructor: `Some` in `Option.Some`.
    ///
    /// This is not available for product type constructors.
    pub con: Option<Name>,

    /// Type arguments explicitly passed to the type. Only empty when not specified. Otherwise there
    /// will be always one element.
    ///
    /// Always empty in patterns.
    ///
    /// E.g. in `Option[U32].Some`, this is `[U32]`.
    pub ty_user_ty_args: Vec<L<Type>>,

    /// Type arguments explicitly passed to the constructor. Only empty when not specified.
    /// Otherwise there will be always one element.
    ///
    /// Always empty in patterns.
    ///
    /// E.g. in `Option.Some[U32]`. this is `[U32]`.
    ///
    /// The parser accepts two type lists at the same time: `Option[t1].Some[t2]`. This use is
    /// rejected by the type checker as the two type argument lists pass the same arguments.
    ///
    /// After type checking, only `ty_args` should be used.
    pub con_user_ty_args: Vec<L<Type>>,

    /// Inferred type arguments of the constructor's type. Filled in by the type checker.
    pub ty_args: Vec<Ty>,

    /// Resolved id for the type (`ty` field). Filled in by the type checker.
    pub resolved_ty_id: Option<Id>,

    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct IfExpr {
    // At least one element
    pub branches: Vec<(L<Expr>, Vec<L<Stmt>>)>,
    pub else_branch: Option<Vec<L<Stmt>>>,
    pub inferred_ty: Option<Ty>,
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

/// `for <pat>: <item_ast_ty> in <expr>: <body>`
#[derive(Debug, Clone)]
pub struct ForStmt {
    pub label: Option<Name>,

    pub pat: L<Pat>,

    /// Type annotation on the loop variable, the `item` type in `Iterator[iter, item, exn]`.
    pub item_ast_ty: Option<L<Type>>,

    pub expr: L<Expr>,

    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub label: Option<Name>,
    pub cond: L<Expr>,
    pub body: Vec<L<Stmt>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    /// A variable: `x`.
    Var(VarExpr),

    /// A constructor: `Option.None`, `Result.Ok`, `Bool.True`, `Vec`.
    ConSel(Con),

    /// A field selection: `<expr>.x` where `x` is a field.
    ///
    /// Parser generates this node for all expression of form `<expr>.<id>`, type checker converts
    /// method selection expressions to `MethodSel`.
    FieldSel(FieldSelExpr),

    /// A method selection: `<expr>.x` where `x` is a method.
    ///
    /// This node is generated by the type checker.
    MethodSel(MethodSelExpr),

    /// An associated function or method selection:
    ///
    /// - Associated function: `Vec.withCapacity` (without `self` parameter).
    /// - Method: `Vec.push` (with `self` parameter), `ToStr.toStr` (trait method).
    AssocFnSel(AssocFnSelExpr),

    /// A function call: `f(a)`.
    Call(CallExpr),

    /// An integer literal.
    Int(IntExpr),

    /// A string literal.
    Str(Vec<StrPart>),

    /// A character literal.
    Char(char),

    /// A binary operator: `x + y`, `i >> 2`.
    ///
    /// Some of the binary operators are desugared to method calls by the type checker.
    BinOp(BinOpExpr),

    /// A unary operator: `-x`, `not b`.
    ///
    /// Some of the unary operators are desugared to method calls by the type checker.
    UnOp(UnOpExpr),

    Return(ReturnExpr),

    Match(MatchExpr),

    If(IfExpr),

    Fn(FnExpr),

    Is(IsExpr),

    Do(DoExpr),

    /// A sequence: `[a, b, c]`, `[a = b, c = d]`, `Vec.[...]`. Can be empty.
    Seq {
        /// The type name: `Vec` in the third example above. `None` in the other examples.
        ty: Option<Name>,

        /// Elements, with optional key part for `<expr> = <expr>` syntax.
        elems: Vec<(Option<L<Expr>>, L<Expr>)>,
    },

    /// A record: `()`, `(x = 123, msg = "hi")`.
    Record(RecordExpr),

    /// A variant: `~Option.Some(123)`, `~123`.
    Variant(VariantExpr),
}

#[derive(Debug, Clone)]
pub struct VarExpr {
    pub mod_prefix: Option<ModulePath>,

    pub name: Name,

    /// Type arguments explicitly passed to the variable. Only empty when not specified. Otherwise
    /// there will be always one element.
    pub user_ty_args: Vec<L<Type>>,

    /// Inferred type arguments of the variable. Filled in by the type checker.
    pub ty_args: Vec<Ty>,

    pub inferred_ty: Option<Ty>,

    /// The resolved variable. Filled in by the type checker. Only available for top-level variable
    /// references.
    pub resolved_id: Option<Id>,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub fun: Box<L<Expr>>,
    pub args: Vec<CallArg>,
    pub splice: Option<Box<L<Expr>>>,
    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct CallArg {
    pub name: Option<Name>,
    pub expr: L<Expr>,
}

/// A field selection: `<expr>.x`.
#[derive(Debug, Clone)]
pub struct FieldSelExpr {
    pub object: Box<L<Expr>>,

    pub field: Name,

    /// Type arguments explicitly passed to the variable. Only empty when not specified. Otherwise
    /// there will be always one element.
    ///
    /// Since fields can't have `forall` quantifiers, this will only be valid when the field is a
    /// method, in which case the type checker will convert this node into `MethodSelExpr`.
    pub user_ty_args: Vec<L<Type>>,

    pub inferred_ty: Option<Ty>,
}

/// A method selection: `<expr>.method`.
///
/// This node is generated by the type checker, from `Expr::FieldSelect`.
///
/// Methods can be associated functions (`Vec.push`), trait methods (`Iterator.next`), local
/// functions (a parameters or `let`), or top-level functions.
///
/// This represents a closure allocation that captures the receiver (first argument) of the method
/// (function being called). We use a different type of expression to be able to recognize it during
/// compilation and optimize it when it's directly called.
#[derive(Debug, Clone)]
pub struct MethodSelExpr {
    /// The reciever, `<expr>` in `<expr>.method`.
    pub object: Box<L<Expr>>,

    /// The function being called.
    pub fun: MethodSelFun,

    /// Type arguments passed to the function.
    pub ty_args: Vec<Ty>,

    /// Inferred type of the expression. Filled in by the type checker.
    pub inferred_ty: Option<Ty>,
}

/// Function being called in a `MethodSelExpr`.
#[derive(Debug, Clone)]
pub enum MethodSelFun {
    Method { ty_id: Id, method_name: Name },
    Local { name: Name },
    TopLevel { local_name: Name, id: Id },
}

/// An associated function or method selection:
///
/// - Associated function: `Vec[U32].withCapacity`.
/// - Method: `Vec.push`.
#[derive(Debug, Clone)]
pub struct AssocFnSelExpr {
    /// Module prefix of the type constructor. E.g. in `Fir/Vec/Vec[U32].withCapacity`,
    /// `Fir/Vec/` part.
    ///
    /// This field is used to resolve the containing type name and it should not be used after type
    /// checking.
    pub mod_prefix: Option<ModulePath>,

    /// The containing type: `Vec` in the examples.
    ///
    /// This field should not be used after type checking. Use `ty_id` to get the containing type.
    pub ty: Name,

    /// Resolved `Id` of `ty`. Filled in by the type checker.
    pub ty_id: Option<Id>,

    /// Type arguments explicitly passed to the constructor. `[U32]` in the first example above.
    ///
    /// Only empty when not specified. Otherwise there will be at least one element.
    pub ty_user_ty_args: Vec<L<Type>>,

    /// The associated function being selected: `withCapacity` and `push` in the examples.
    pub member: Name,

    /// Type arguments explicitly passed to the variable.
    ///
    /// Only empty when not specified. Otherwise there will be at least one element.
    pub user_ty_args: Vec<L<Type>>,

    /// Inferred type arguments of the type and associated function. Filled in by the type checker.
    pub ty_args: Vec<Ty>,

    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct BinOpExpr {
    pub left: Box<L<Expr>>,
    pub right: Box<L<Expr>>,
    pub op: BinOp,
    // Note: we don't need an `inferred_ty` field here as most of the binops are desugared during
    // type checking, only the bool `and` and `or` are left (as they have special evaluation rules).
    // So the inferred types are always `Bool` after type checking.
}

#[derive(Debug, Clone)]
pub struct UnOpExpr {
    pub op: UnOp,
    pub expr: Box<L<Expr>>,
    // Note: we don't need an `inferred_ty` field here as these exprs are desugared during type
    // checking.
}

#[derive(Debug, Clone)]
pub struct ReturnExpr {
    pub expr: Box<L<Expr>>,

    /// Inferred type of this expression. Filled in by the type checker.
    ///
    /// Note that this is different than the returned expression's (`expr`) type. For example:
    ///
    /// ```ignore
    /// f(x, return "hi", y)
    /// ```
    ///
    /// Here the returned expression's type is `Str`, but the `return` expression's type will depend
    /// on the `f`'s second argument type.
    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct IntExpr {
    /// The integer token contents. This includes the sign and radix parts, when available.
    /// Examples: `-0xabc`, `0b1010`, `123`.
    pub text: SmolStr,

    /// The type checker updates this based on the inferred type of the integer.
    pub kind: Option<IntKind>,

    /// Absolute value of the parsed integer.
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

#[derive(Debug, Clone)]
pub struct DoExpr {
    pub stmts: Vec<L<Stmt>>,
    pub inferred_ty: Option<Ty>,
}

/// A record expression, e.g.
/// - `()` (empty record)
/// - `(msg = "hi")` (single field)
/// - `(msg = "hi", x = 123,)` (multiple fields, with trailing comma)
/// - `(msg = "hi", ..f())` (with splicing)
#[derive(Debug, Clone)]
pub struct RecordExpr {
    /// Named fields of the reocrd, before any splicing.
    pub fields: Vec<(Name, L<Expr>)>,

    /// Record splice: `(msg = "hi", ..<expr>)`.
    pub splice: Option<Box<L<Expr>>>,

    /// Inferred type of the record, filled in by the type checker.
    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct VariantExpr {
    pub expr: Box<L<Expr>>,
    pub inferred_ty: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct ImportDecl {
    /// Attributes of the import declaration. E.g. `#[NoImplicitPrelude]`, `#[include(...)]`.
    pub attrs: Vec<Attribute>,
    pub items: Vec<ImportItem>,
}

/// A single import item in an `import [...]` list. Examples:
///
/// - `A/B/C` imports everything from `A/B/C`. Imported definitions used directly, without prefix.
/// - `A/B/C as D` imports `A/B/C` as module, with name `D`. Imported definitions used with `D/...`
///   prefix.
/// - `A/B/C/[f1, Type1]` imports listed things from `A/B/C`. Imported definitions used directly.
/// - `A/B/C/[f1 as _f1, Type1 as Type2]` imports listed things with different names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportItem {
    /// `A/B/C` in the examples.
    pub path: ModulePath,

    /// Specifies what to import, and how, from the `path`.
    ///
    /// If not available, everything exported from the module is imported and used directly (without
    /// prefix or renaming).
    pub import_spec: Option<ImportSpec>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportSpec {
    /// Import the module with a prefix. E.g.
    /// - `A/B/C as D`: prefix = `D`.
    Prefixed { prefix: SmolStr },

    /// Import given list of things, potentially with new names.
    Selective { names: Vec<ImportName> },
}

/// An imported name. E.g. in `A/B/C/[foo, bar as _bar]`, we have
/// - `foo`: original_name = `foo`, local_name = `foo`
/// - `bar as _bar`: original_name = `bar`, local_name = `_bar`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportName {
    /// The name of the imported thing, in the module being imported.
    pub original_name: SmolStr,

    /// The name of the imported thing, in the importing module.
    pub local_name: SmolStr,
}

#[derive(Debug, Clone)]
pub struct TraitDecl {
    /// Trait name.
    pub name: L<Name>,

    /// Type parameters of the trait.
    pub type_params: Vec<TypeParam>,

    /// Kinds of `type_params`. Filled in by kind inference.
    pub type_param_kinds: Vec<Kind>,

    /// Method and associated types of the trait.
    pub items: Vec<TraitDeclItem>,
}

#[derive(Debug, Clone)]
pub enum TraitDeclItem {
    /// An associated type declaration, with optionl kind. Kind defaults to `*`.
    /// - `type Foo`: no kind annotation, defaults to `*`
    /// - `type Ext: Row[Rec]`: (with kind annotation)
    Type {
        name: L<Name>,
        kind: Option<L<Type>>,
        default: Option<L<Type>>,
    },

    Fun(L<FunDecl>),
}

/// Type parameter and predicates of an `impl` or function.
///
/// E.g. `[Iterator[iter, item], Debug[item]]`.
#[derive(Debug, Clone, Default)]
pub struct Context {
    /// Type parameters, generated by the type checker.
    pub type_params: Vec<(Name, Kind)>,

    /// Predicates: `Iterator[iter, item]` and `Debug[item]` in the example.
    pub preds: Vec<L<Pred>>,
}

/// A predicate in a context. E.g. in context
///
/// ```ignore
/// [ext: Row[Rec], Iterator[iter, exn], Iterator[iter, exn].Item = U32]
/// ```
///
/// Predicates:
///
/// - `ext: Row[Rec]` is a `Pred::Kind`
/// - `Iterator[iter, exn]` is a `Pred::App`
/// - `Iterator[iter, exn].Item = U32` is a `Pred::AssocTyEq`
#[derive(Debug, Clone)]
pub enum Pred {
    /// A kind annotation: `ext: Row[Rec]` in the example.
    ///
    /// The kind part is optional, kinds defaulted as `*`.
    Kind { var: Name, kind: Option<L<Type>> },

    /// A trait application: `Iterator[iter, exn]` in the example.
    App(NamedType),

    /// An associated type equality: `Iterator[iter, exn].Item = U32` in the example.
    AssocTyEq {
        ty: NamedType,
        assoc_ty: Name,
        eq: L<Type>,
    },
}

/// An `impl` block, implementing a trait for a type.
///
/// ```ignore
/// impl[ToStr[a]] ToStr[Vec[a]]:
///   toStr(self) Str: ...
///
/// impl Iterator[VecIter[a], a]:
///   next(self) Option[a]: ...
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
    pub trait_: L<Name>,

    /// Type parameters of the trait.
    ///
    /// In the example: `[Vec[a]]`.
    pub tys: Vec<L<Type>>,

    /// Method and associated type implementations.
    pub items: Vec<ImplDeclItem>,
}

#[derive(Debug, Clone)]
pub enum ImplDeclItem {
    Type { assoc_ty: L<Name>, rhs: L<Type> },
    Fun(L<FunDecl>),
}

/// An attribute: `#[derive(Foo, Bar)]`, `#[path = Fir/Prim/U32]`.
///
/// This just uses expression syntax as expression syntax should be rich enough to cover most
/// attributes. We may revise this as needed.
#[derive(Debug, Clone)]
pub struct Attribute {
    pub lhs: Option<L<Expr>>,
    pub expr: L<Expr>,
}

impl Type {
    /// Substitute star-kinded `ty` for `var` in `self`.
    pub fn subst_id(&self, var: &Name, ty: &Type) -> Type {
        self.subst_ids(&[(var.clone(), ty.clone())].into_iter().collect())
    }

    pub fn subst_ids(&self, substs: &HashMap<Name, Type>) -> Type {
        match self {
            Type::Named(NamedType {
                mod_prefix: _,
                name,
                args,
            }) => Type::Named(NamedType {
                mod_prefix: None,
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
                let fields: Vec<(Name, L<Type>)> = fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), ty.map_as_ref(|ty| ty.subst_ids(substs))))
                    .collect();

                let extension = extension
                    .as_ref()
                    .map(|ext| Box::new(ext.map_as_ref(|ty| ty.subst_ids(substs))));

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
                let alts: Vec<NamedType> = alts
                    .iter()
                    .map(
                        |NamedType {
                             mod_prefix: _,
                             name,
                             args,
                         }| NamedType {
                            mod_prefix: None,
                            name: name.clone(),
                            args: args
                                .iter()
                                .map(|L { loc, node }| L {
                                    loc: loc.clone(),
                                    node: node.subst_ids(substs),
                                })
                                .collect(),
                        },
                    )
                    .collect();

                let extension = extension
                    .as_ref()
                    .map(|ext| Box::new(ext.map_as_ref(|ty| ty.subst_ids(substs))));

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

            Type::AssocTySelect { ty, assoc_ty } => Type::AssocTySelect {
                ty: ty.map_as_ref(|ty| Box::new(ty.subst_ids(substs))),
                assoc_ty: assoc_ty.clone(),
            },
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
    pub fn subst_ty_ids(&mut self, substs: &HashMap<Name, Type>) {
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

            Stmt::Expr(expr) => expr.subst_ty_ids(substs),

            Stmt::For(ForStmt {
                label: _,
                pat: _,
                item_ast_ty,
                expr,
                body,
            }) => {
                if let Some(ast_ty) = item_ast_ty {
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
    pub fn subst_ty_ids(&mut self, substs: &HashMap<Name, Type>) {
        match self {
            Expr::ConSel(_) | Expr::Int(_) | Expr::Char(_) => {}

            Expr::Var(VarExpr {
                mod_prefix: _,
                name: _,
                user_ty_args,
                ty_args,
                inferred_ty,
                resolved_id: _,
            }) => {
                assert!(inferred_ty.is_none());
                assert!(ty_args.is_empty());
                for ty_arg in user_ty_args.iter_mut() {
                    ty_arg.node = ty_arg.node.subst_ids(substs);
                }
            }

            Expr::AssocFnSel(AssocFnSelExpr {
                mod_prefix: _,
                ty: _,
                ty_id: _,
                ty_user_ty_args,
                member: _,
                user_ty_args,
                ty_args,
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
                assert!(ty_args.is_empty());
                for ty_arg in ty_user_ty_args.iter_mut() {
                    ty_arg.node = ty_arg.node.subst_ids(substs);
                }
                for ty_arg in user_ty_args.iter_mut() {
                    ty_arg.node = ty_arg.node.subst_ids(substs);
                }
            }

            Expr::FieldSel(FieldSelExpr {
                object,
                field: _,
                user_ty_args,
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
                object.node.subst_ty_ids(substs);
                for ty_arg in user_ty_args.iter_mut() {
                    ty_arg.node = ty_arg.node.subst_ids(substs);
                }
            }

            Expr::MethodSel(MethodSelExpr {
                object,
                fun: _,
                ty_args,
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
                assert!(ty_args.is_empty());
                object.node.subst_ty_ids(substs);
            }

            Expr::Call(CallExpr {
                fun,
                args,
                splice,
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
                fun.node.subst_ty_ids(substs);
                for CallArg { name: _, expr } in args {
                    expr.node.subst_ty_ids(substs);
                }
                if let Some(expr) = splice {
                    expr.node.subst_ty_ids(substs);
                }
            }

            Expr::Str(parts) => {
                for part in parts {
                    match part {
                        StrPart::Str(_) => {}
                        StrPart::Expr(expr) => expr.node.subst_ty_ids(substs),
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

            Expr::Return(ReturnExpr { expr, inferred_ty }) => {
                assert!(inferred_ty.is_none());
                expr.node.subst_ty_ids(substs)
            }

            Expr::Match(MatchExpr {
                scrutinee,
                alts,
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
                scrutinee.node.subst_ty_ids(substs);
                for Alt { pat: _, guard, rhs } in alts {
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
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
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
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
                sig.subst_ty_ids(substs);
                for stmt in body {
                    stmt.node.subst_ty_ids(substs);
                }
            }

            Expr::Is(IsExpr { expr, pat: _ }) => {
                expr.node.subst_ty_ids(substs);
            }

            Expr::Do(DoExpr { stmts, inferred_ty }) => {
                assert!(inferred_ty.is_none());
                for stmt in stmts {
                    stmt.node.subst_ty_ids(substs);
                }
            }

            Expr::Seq { ty: _, elems } => {
                for (k, v) in elems {
                    if let Some(k) = k {
                        k.node.subst_ty_ids(substs);
                    }
                    v.node.subst_ty_ids(substs);
                }
            }

            Expr::Record(RecordExpr {
                fields,
                splice,
                inferred_ty,
            }) => {
                assert!(inferred_ty.is_none());
                for (_field_name, field_expr) in fields {
                    field_expr.node.subst_ty_ids(substs);
                }
                if let Some(expr) = splice {
                    expr.node.subst_ty_ids(substs);
                }
            }

            Expr::Variant(VariantExpr { expr, inferred_ty }) => {
                assert!(inferred_ty.is_none());
                expr.node.subst_ty_ids(substs);
            }
        }
    }

    pub fn inferred_ty(&self) -> Option<Ty> {
        match self {
            Expr::Var(VarExpr { inferred_ty, .. })
            | Expr::ConSel(Con { inferred_ty, .. })
            | Expr::FieldSel(FieldSelExpr { inferred_ty, .. })
            | Expr::MethodSel(MethodSelExpr { inferred_ty, .. })
            | Expr::AssocFnSel(AssocFnSelExpr { inferred_ty, .. })
            | Expr::Call(CallExpr { inferred_ty, .. })
            | Expr::Return(ReturnExpr { inferred_ty, .. })
            | Expr::Match(MatchExpr { inferred_ty, .. })
            | Expr::If(IfExpr { inferred_ty, .. })
            | Expr::Fn(FnExpr { inferred_ty, .. })
            | Expr::Do(DoExpr { inferred_ty, .. })
            | Expr::Record(RecordExpr { inferred_ty, .. })
            | Expr::Variant(VariantExpr { inferred_ty, .. }) => inferred_ty.clone(),

            Expr::Int(IntExpr { kind, .. }) => {
                let id = match kind.as_ref()? {
                    IntKind::I8(_) => builtin_ids::I8(),
                    IntKind::U8(_) => builtin_ids::U8(),
                    IntKind::I32(_) => builtin_ids::I32(),
                    IntKind::U32(_) => builtin_ids::U32(),
                    IntKind::I64(_) => builtin_ids::I64(),
                    IntKind::U64(_) => builtin_ids::U64(),
                };
                Some(Ty::Con(id, Kind::Star))
            }

            Expr::Str(_) => Some(Ty::str()),

            Expr::Char(_) => Some(Ty::char()),

            Expr::Is(_)
            | Expr::BinOp(BinOpExpr {
                op: BinOp::And | BinOp::Or,
                ..
            }) => Some(Ty::bool()),

            // Rest of the expressions will be desugared by the type checker.
            Expr::BinOp(_) | Expr::UnOp(_) | Expr::Seq { .. } => None,
        }
    }
}

impl FunSig {
    pub fn subst_ty_ids(&mut self, substs: &HashMap<Name, Type>) {
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
