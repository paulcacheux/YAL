#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    start: usize,
    end: usize,
}

impl Span {
    pub fn new(start: usize, end: usize) -> Self {
        Span { start, end }
    }

    pub fn new_one(start: usize) -> Self {
        Span::new(start, start + 1)
    }

    pub fn new_with_len(start: usize, len: usize) -> Self {
        Span::new(start, start + len)
    }

    pub fn merge(start: Span, end: Span) -> Self {
        Span {
            start: start.start,
            end: end.end
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span
}

impl<T> Spanned<T> {
    pub fn new(inner: T, span: Span) -> Self {
        Spanned {
            inner,
            span
        }
    }
}
