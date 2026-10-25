// The lexer: source bytes to tokens. A token records whether a newline came
// before it, which is how the parser ends statements without `;`.

use crate::diag::{Diag, Span};

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Ident(String),
    Int(u64),
    Float(f64),
    Str(Vec<u8>),
    /// `'a'`: a byte.
    Char(u8),

    // keywords
    Fn,
    Let,
    Var,
    Return,
    If,
    Else,
    While,
    Loop,
    For,
    In,
    Break,
    Continue,
    True,
    False,
    Struct,
    Enum,
    Match,
    Impl,
    Trait,
    Pub,
    Import,
    As,
    Const,
    Comptime,
    Extern,
    Export,
    Unsafe,
    Sink,
    Inout,
    Ref,
    Move,
    Type,
    Static,

    // punctuation
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Dot,
    DotDot,
    Ellipsis,
    Comma,
    Colon,
    Semi,
    Arrow,
    FatArrow,
    Question,
    Hash,
    HashBang,
    Assign,
    /// `+=`, `-=`, ...: the operator.
    OpAssign(Op),
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusWrap,
    MinusWrap,
    StarWrap,
    Amp,
    Pipe,
    Caret,
    Shl,
    Shr,
    Bang,
    AndAnd,
    OrOr,

    Eof,
}

/// Binary operators, as tokens name them; also the operator of `op=`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Op {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    AddWrap,
    SubWrap,
    MulWrap,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    LogAnd,
    LogOr,
}

impl Op {
    pub fn text(self) -> &'static str {
        match self {
            Op::Add => "+",
            Op::Sub => "-",
            Op::Mul => "*",
            Op::Div => "/",
            Op::Rem => "%",
            Op::AddWrap => "+%",
            Op::SubWrap => "-%",
            Op::MulWrap => "*%",
            Op::And => "&",
            Op::Or => "|",
            Op::Xor => "^",
            Op::Shl => "<<",
            Op::Shr => ">>",
            Op::Eq => "==",
            Op::Ne => "!=",
            Op::Lt => "<",
            Op::Le => "<=",
            Op::Gt => ">",
            Op::Ge => ">=",
            Op::LogAnd => "&&",
            Op::LogOr => "||",
        }
    }

    pub fn is_compare(self) -> bool {
        matches!(self, Op::Eq | Op::Ne | Op::Lt | Op::Le | Op::Gt | Op::Ge)
    }
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
    pub nl_before: bool,
}

pub fn keyword(s: &str) -> Option<Tok> {
    Some(match s {
        "fn" => Tok::Fn,
        "let" => Tok::Let,
        "var" => Tok::Var,
        "return" => Tok::Return,
        "if" => Tok::If,
        "else" => Tok::Else,
        "while" => Tok::While,
        "loop" => Tok::Loop,
        "for" => Tok::For,
        "in" => Tok::In,
        "break" => Tok::Break,
        "continue" => Tok::Continue,
        "true" => Tok::True,
        "false" => Tok::False,
        "struct" => Tok::Struct,
        "enum" => Tok::Enum,
        "match" => Tok::Match,
        "impl" => Tok::Impl,
        "trait" => Tok::Trait,
        "pub" => Tok::Pub,
        "import" => Tok::Import,
        "as" => Tok::As,
        "const" => Tok::Const,
        "comptime" => Tok::Comptime,
        "extern" => Tok::Extern,
        "export" => Tok::Export,
        "unsafe" => Tok::Unsafe,
        "sink" => Tok::Sink,
        "inout" => Tok::Inout,
        "ref" => Tok::Ref,
        "move" => Tok::Move,
        "type" => Tok::Type,
        "static" => Tok::Static,
        _ => return None,
    })
}

pub fn lex(file: u32, src: &[u8]) -> Result<Vec<Token>, Diag> {
    let mut out = Vec::new();
    let mut i = 0usize;
    let mut nl = true;
    let n = src.len();
    let at = |i: usize| -> u8 {
        if i < n {
            src[i]
        } else {
            0
        }
    };
    loop {
        // trivia
        loop {
            let c = at(i);
            if c == b'\n' {
                nl = true;
                i += 1;
            } else if c == b' ' || c == b'\t' || c == b'\r' {
                i += 1;
            } else if c == b'/' && at(i + 1) == b'/' {
                while i < n && src[i] != b'\n' {
                    i += 1;
                }
            } else if c == b'/' && at(i + 1) == b'*' {
                let start = i;
                let mut depth = 0;
                loop {
                    if i >= n {
                        return Err(Diag::new(Span::new(file, start, start + 2), "unterminated comment"));
                    }
                    if src[i] == b'/' && at(i + 1) == b'*' {
                        depth += 1;
                        i += 2;
                    } else if src[i] == b'*' && at(i + 1) == b'/' {
                        depth -= 1;
                        i += 2;
                        if depth == 0 {
                            break;
                        }
                    } else {
                        if src[i] == b'\n' {
                            nl = true;
                        }
                        i += 1;
                    }
                }
            } else {
                break;
            }
        }
        let start = i;
        if i >= n {
            out.push(Token { tok: Tok::Eof, span: Span::new(file, n, n), nl_before: true });
            return Ok(out);
        }
        let c = src[i];
        let tok = if c.is_ascii_alphabetic() || c == b'_' {
            while at(i).is_ascii_alphanumeric() || at(i) == b'_' {
                i += 1;
            }
            let s = std::str::from_utf8(&src[start..i]).unwrap();
            keyword(s).unwrap_or_else(|| Tok::Ident(s.to_string()))
        } else if c.is_ascii_digit() {
            let after_dot = matches!(out.last(), Some(Token { tok: Tok::Dot, .. }));
            number(file, src, &mut i, !after_dot)?
        } else if c == b'"' {
            i += 1;
            let mut bytes = Vec::new();
            loop {
                if i >= n || src[i] == b'\n' {
                    return Err(Diag::new(Span::new(file, start, i), "unterminated string"));
                }
                let c = src[i];
                i += 1;
                if c == b'"' {
                    break;
                }
                if c == b'\\' {
                    bytes.push(escape(file, src, &mut i)?);
                } else {
                    bytes.push(c);
                }
            }
            Tok::Str(bytes)
        } else if c == b'\'' {
            i += 1;
            let b = if at(i) == b'\\' {
                i += 1;
                escape(file, src, &mut i)?
            } else {
                i += 1;
                at(i - 1)
            };
            if at(i) != b'\'' {
                return Err(Diag::new(Span::new(file, start, i), "a character literal is one byte between quotes"));
            }
            i += 1;
            Tok::Char(b)
        } else {
            let c1 = at(i + 1);
            let c2 = at(i + 2);
            let (t, len) = match (c, c1) {
                (b'(', _) => (Tok::LParen, 1),
                (b')', _) => (Tok::RParen, 1),
                (b'{', _) => (Tok::LBrace, 1),
                (b'}', _) => (Tok::RBrace, 1),
                (b'[', _) => (Tok::LBracket, 1),
                (b']', _) => (Tok::RBracket, 1),
                (b'.', b'.') if c2 == b'.' => (Tok::Ellipsis, 3),
                (b'.', b'.') => (Tok::DotDot, 2),
                (b'.', _) => (Tok::Dot, 1),
                (b',', _) => (Tok::Comma, 1),
                (b':', _) => (Tok::Colon, 1),
                (b';', _) => (Tok::Semi, 1),
                (b'?', _) => (Tok::Question, 1),
                (b'#', b'!') => (Tok::HashBang, 2),
                (b'#', _) => (Tok::Hash, 1),
                (b'-', b'>') => (Tok::Arrow, 2),
                (b'=', b'>') => (Tok::FatArrow, 2),
                (b'=', b'=') => (Tok::EqEq, 2),
                (b'=', _) => (Tok::Assign, 1),
                (b'!', b'=') => (Tok::NotEq, 2),
                (b'!', _) => (Tok::Bang, 1),
                (b'<', b'<') if c2 == b'=' => (Tok::OpAssign(Op::Shl), 3),
                (b'<', b'<') => (Tok::Shl, 2),
                (b'<', b'=') => (Tok::Le, 2),
                (b'<', _) => (Tok::Lt, 1),
                (b'>', b'>') if c2 == b'=' => (Tok::OpAssign(Op::Shr), 3),
                (b'>', b'>') => (Tok::Shr, 2),
                (b'>', b'=') => (Tok::Ge, 2),
                (b'>', _) => (Tok::Gt, 1),
                (b'&', b'&') => (Tok::AndAnd, 2),
                (b'&', b'=') => (Tok::OpAssign(Op::And), 2),
                (b'&', _) => (Tok::Amp, 1),
                (b'|', b'|') => (Tok::OrOr, 2),
                (b'|', b'=') => (Tok::OpAssign(Op::Or), 2),
                (b'|', _) => (Tok::Pipe, 1),
                (b'^', b'=') => (Tok::OpAssign(Op::Xor), 2),
                (b'^', _) => (Tok::Caret, 1),
                (b'+', b'%') if c2 == b'=' => (Tok::OpAssign(Op::AddWrap), 3),
                (b'+', b'%') => (Tok::PlusWrap, 2),
                (b'+', b'=') => (Tok::OpAssign(Op::Add), 2),
                (b'+', _) => (Tok::Plus, 1),
                (b'-', b'%') if c2 == b'=' => (Tok::OpAssign(Op::SubWrap), 3),
                (b'-', b'%') => (Tok::MinusWrap, 2),
                (b'-', b'=') => (Tok::OpAssign(Op::Sub), 2),
                (b'-', _) => (Tok::Minus, 1),
                (b'*', b'%') if c2 == b'=' => (Tok::OpAssign(Op::MulWrap), 3),
                (b'*', b'%') => (Tok::StarWrap, 2),
                (b'*', b'=') => (Tok::OpAssign(Op::Mul), 2),
                (b'*', _) => (Tok::Star, 1),
                (b'/', b'=') => (Tok::OpAssign(Op::Div), 2),
                (b'/', _) => (Tok::Slash, 1),
                (b'%', b'=') => (Tok::OpAssign(Op::Rem), 2),
                (b'%', _) => (Tok::Percent, 1),
                _ => {
                    let ch = std::str::from_utf8(&src[i..(i + 4).min(n)])
                        .ok()
                        .and_then(|s| s.chars().next())
                        .map(|c| c.to_string())
                        .unwrap_or_else(|| format!("byte 0x{:02x}", c));
                    return Err(Diag::new(Span::new(file, i, i + 1), &format!("unexpected character `{}`", ch)));
                }
            };
            i += len;
            t
        };
        out.push(Token { tok, span: Span::new(file, start, i), nl_before: nl });
        nl = false;
    }
}

fn escape(file: u32, src: &[u8], i: &mut usize) -> Result<u8, Diag> {
    let start = *i - 1;
    let c = src.get(*i).copied().unwrap_or(0);
    *i += 1;
    Ok(match c {
        b'n' => b'\n',
        b't' => b'\t',
        b'r' => b'\r',
        b'0' => 0,
        b'\\' => b'\\',
        b'\'' => b'\'',
        b'"' => b'"',
        b'x' => {
            let h = |c: u8| (c as char).to_digit(16);
            match (src.get(*i).and_then(|&c| h(c)), src.get(*i + 1).and_then(|&c| h(c))) {
                (Some(a), Some(b)) => {
                    *i += 2;
                    (a * 16 + b) as u8
                }
                _ => return Err(Diag::new(Span::new(file, start, *i), "`\\x` takes two hex digits")),
            }
        }
        _ => return Err(Diag::new(Span::new(file, start, *i), "unknown escape")),
    })
}

fn number(file: u32, src: &[u8], i: &mut usize, allow_float: bool) -> Result<Tok, Diag> {
    let start = *i;
    let at = |i: usize| src.get(i).copied().unwrap_or(0);
    let (radix, skip) = match (at(*i), at(*i + 1)) {
        (b'0', b'x') => (16, 2),
        (b'0', b'b') => (2, 2),
        (b'0', b'o') => (8, 2),
        _ => (10, 0),
    };
    *i += skip;
    let mut digits = String::new();
    let digit = |c: u8| if radix == 10 { c.is_ascii_digit() } else { c.is_ascii_alphanumeric() };
    while digit(at(*i)) || at(*i) == b'_' {
        if at(*i) != b'_' {
            digits.push(at(*i) as char);
        }
        *i += 1;
    }
    let mut float = false;
    if allow_float && radix == 10 && at(*i) == b'.' && at(*i + 1).is_ascii_digit() {
        float = true;
        digits.push('.');
        *i += 1;
        while at(*i).is_ascii_digit() || at(*i) == b'_' {
            if at(*i) != b'_' {
                digits.push(at(*i) as char);
            }
            *i += 1;
        }
    }
    if allow_float && radix == 10 && (at(*i) == b'e' || at(*i) == b'E') {
        let mut j = *i + 1;
        if at(j) == b'+' || at(j) == b'-' {
            j += 1;
        }
        if at(j).is_ascii_digit() {
            float = true;
            digits.push('e');
            digits.push_str(std::str::from_utf8(&src[*i + 1..j]).unwrap());
            *i = j;
            while at(*i).is_ascii_digit() {
                digits.push(at(*i) as char);
                *i += 1;
            }
        }
    }
    let span = Span::new(file, start, *i);
    if at(*i).is_ascii_alphanumeric() || at(*i) == b'_' {
        return Err(Diag::new(span, "malformed number"));
    }
    if float {
        return digits.parse::<f64>().map(Tok::Float).map_err(|_| Diag::new(span, "malformed float literal"));
    }
    u64::from_str_radix(&digits, radix)
        .map(Tok::Int)
        .map_err(|_| Diag::new(span, "malformed or too large integer literal"))
}
