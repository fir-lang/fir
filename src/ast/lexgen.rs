//! Lexer generator AST.

use crate::ast::*;

#[derive(Debug, Clone)]
pub struct LexerDecl {
    pub type_name: Id,
    pub user_state_type: Option<Type>,
    pub token_type: Type,
    pub rules: Vec<Rule>,
}

#[derive(Debug, Clone)]
pub enum Rule {
    /// `type Error = UserError;`
    ErrorType {
        /// Type on the RHS, e.g. `UserError`
        ty: Type,
    },

    /// A list of named rules at the top level: `rule <Ident> { <rules> },`
    RuleSet {
        name: Id,
        rules: Vec<RuleOrBinding>,
    },
}

#[derive(Debug, Clone)]
pub enum RuleOrBinding {
    Rule(SingleRule),
    Binding(Binding),
}

#[derive(Debug, Clone)]
pub struct SingleRule {
    pub lhs: RegexCtx,
    pub rhs: Vec<L<Stmt>>,
}

/// A named regex binding: `let <ident> = <regex>;`.
#[derive(Debug, Clone)]
pub struct Binding {
    pub var: Id,
    pub re: Regex,
}

/// Regular expression with optional right context (lookahead)
#[derive(Debug, Clone)]
pub struct RegexCtx {
    pub re: Regex,
    pub right_ctx: Option<Regex>,
}

#[derive(Debug, Clone)]
pub enum Regex {
    Var(Id),
    Char(char),
    String(String),
    CharSet(CharSet),
    ZeroOrMore(Box<Regex>),
    OneOrMore(Box<Regex>),
    ZeroOrOne(Box<Regex>),
    Concat(Box<Regex>, Box<Regex>),
    Or(Box<Regex>, Box<Regex>),
    Any, // any character
    EndOfInput,

    /// Difference, or exclusion: characters in the first regex, excluding characters in the second
    /// regex.
    Diff(Box<Regex>, Box<Regex>),
}

#[derive(Debug, Clone)]
pub struct CharSet(pub Vec<CharOrRange>);

#[derive(Debug, Clone, Copy)]
pub enum CharOrRange {
    Char(char),
    Range(char, char),
}
