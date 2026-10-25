// Source positions and error messages.

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub file: u32,
    pub lo: u32,
    pub hi: u32,
}

impl Span {
    pub fn new(file: u32, lo: usize, hi: usize) -> Span {
        Span { file, lo: lo as u32, hi: hi as u32 }
    }

    pub fn to(self, other: Span) -> Span {
        if self.file != other.file {
            return self;
        }
        Span { file: self.file, lo: self.lo.min(other.lo), hi: self.hi.max(other.hi) }
    }
}

#[derive(Clone, Debug)]
pub struct Diag {
    pub span: Span,
    pub msg: String,
    /// Further lines: where the instance came from, a hint.
    pub notes: Vec<(Option<Span>, String)>,
}

impl Diag {
    pub fn new(span: Span, msg: &str) -> Diag {
        Diag { span, msg: msg.to_string(), notes: Vec::new() }
    }

    pub fn note(mut self, span: Option<Span>, msg: &str) -> Diag {
        self.notes.push((span, msg.to_string()));
        self
    }
}

pub struct SourceFile {
    pub path: String,
    pub text: Vec<u8>,
}

#[derive(Default)]
pub struct Sources {
    pub files: Vec<SourceFile>,
}

impl Sources {
    pub fn add(&mut self, path: String, text: Vec<u8>) -> u32 {
        self.files.push(SourceFile { path, text });
        (self.files.len() - 1) as u32
    }

    /// 1-based line and column of a byte offset.
    pub fn line_col(&self, span: Span) -> (usize, usize) {
        let Some(f) = self.files.get(span.file as usize) else {
            return (0, 0);
        };
        let lo = (span.lo as usize).min(f.text.len());
        let mut line = 1;
        let mut col = 1;
        for &b in &f.text[..lo] {
            if b == b'\n' {
                line += 1;
                col = 1;
            } else {
                col += 1;
            }
        }
        (line, col)
    }

    pub fn where_(&self, span: Span) -> String {
        let (l, c) = self.line_col(span);
        let path = self.files.get(span.file as usize).map(|f| f.path.as_str()).unwrap_or("?");
        format!("{}:{}:{}", path, l, c)
    }

    pub fn render(&self, d: &Diag) -> String {
        let mut s = format!("error: {}: {}", self.where_(d.span), d.msg);
        if let Some(f) = self.files.get(d.span.file as usize) {
            let lo = (d.span.lo as usize).min(f.text.len());
            let ls = f.text[..lo].iter().rposition(|&b| b == b'\n').map(|p| p + 1).unwrap_or(0);
            let le = f.text[lo..].iter().position(|&b| b == b'\n').map(|p| p + lo).unwrap_or(f.text.len());
            let line = String::from_utf8_lossy(&f.text[ls..le]);
            let width = ((d.span.hi as usize).min(le).max(lo + 1)) - lo;
            s.push_str(&format!("\n    {}\n    {}{}", line, " ".repeat(lo - ls), "^".repeat(width)));
        }
        for (sp, n) in &d.notes {
            match sp {
                Some(sp) => s.push_str(&format!("\nnote: {}: {}", self.where_(*sp), n)),
                None => s.push_str(&format!("\nnote: {}", n)),
            }
        }
        s
    }
}
