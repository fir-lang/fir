pub struct Printer {
    indent: u32,
    buf: String,

    /// Whether to push the indentation on next push (char or str).
    ///
    /// This is to avoid lines with just whitespace when we generate empty lines. If we generate
    /// indentation right after a `nl`, empty lines get indented.
    push_indent: bool,
}

impl Printer {
    pub fn new() -> Printer {
        Printer {
            indent: 0,
            buf: String::new(),
            push_indent: false,
        }
    }

    pub fn indent(&mut self) {
        self.indent += 1;
    }

    pub fn dedent(&mut self) {
        self.indent -= 1;
    }

    pub fn indented<F>(&mut self, f: F)
    where
        F: FnOnce(&mut Printer),
    {
        self.indent();
        f(self);
        self.dedent();
    }

    pub fn nl(&mut self) {
        self.buf.push('\n');
        self.push_indent = true;
    }

    pub fn char(&mut self, c: char) {
        self.push_indent();
        self.buf.push(c);
    }

    pub fn str(&mut self, s: &str) {
        self.push_indent();
        self.buf.push_str(s);
    }

    /// Print items from `iter`, inserting `separator` between consecutive items.
    pub fn sep<T, I, F>(&mut self, iter: I, separator: &str, mut f: F)
    where
        I: IntoIterator<Item = T>,
        F: FnMut(&mut Printer, T),
    {
        for (i, item) in iter.into_iter().enumerate() {
            if i != 0 {
                self.str(separator);
            }
            f(self, item);
        }
    }

    pub fn as_str(&self) -> &str {
        &self.buf
    }

    pub fn finish(self) -> String {
        self.buf
    }

    fn push_indent(&mut self) {
        if self.push_indent {
            for _ in 0..self.indent {
                self.buf.push_str("    ");
            }
            self.push_indent = false;
        }
    }
}

impl std::fmt::Write for Printer {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        self.str(s);
        Ok(())
    }
}
