#![allow(unused)]

use crate::ast;

pub fn loc_display(loc: &ast::Loc) -> impl std::fmt::Display + '_ {
    LocDisplay(loc)
}

struct LocDisplay<'a>(&'a ast::Loc);

impl std::fmt::Display for LocDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}",
            self.0.module,
            self.0.line_start + 1,
            self.0.col_start + 1
        )
    }
}

pub fn span_display(loc: &ast::Loc) -> impl std::fmt::Display + '_ {
    SpanDisplay(loc)
}

struct SpanDisplay<'a>(&'a ast::Loc);

impl std::fmt::Display for SpanDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}:{}-{}:{}",
            self.0.module,
            self.0.line_start + 1,
            self.0.col_start + 1,
            self.0.line_end + 1,
            self.0.col_end + 1,
        )
    }
}
