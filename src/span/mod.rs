use string_interner::symbol::SymbolU32 as InternedString;

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

impl From<std::ops::Range<usize>> for Span {
    fn from(value: std::ops::Range<usize>) -> Self {
        Self {
            lo: value.start,
            hi: value.end,
        }
    }
}

impl std::fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Span({}..{})", self.lo, self.hi)
    }
}

impl Span {
    pub fn new(lo: usize, hi: usize) -> Span {
        assert!(lo <= hi);
        Self { lo, hi }
    }

    pub fn dummy() -> Self {
        Self { lo: 0, hi: 0 }
    }
}

impl Default for Span {
    fn default() -> Self {
        Self::dummy()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct Ident {
    pub name: InternedString,
    pub span: Span,
}

impl std::fmt::Debug for Ident {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Ident({:?}, {}..{})",
            self.name, self.span.lo, self.span.hi
        )
    }
}
