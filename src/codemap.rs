#[derive(Debug, Clone)]
pub struct CodeMap<'name, 'input> {
    input_name: &'name str,
    lines: Vec<(usize, &'input str)>,
}

impl<'name, 'input> CodeMap<'name, 'input> {
    pub fn new(input_name: &'name str, input: &'input str) -> Self {
        let mut lines = Vec::new();
        let mut start_index = 0;

        fn string_builder(input: &str, start: usize, end: usize) -> &str {
            let s = &input[start..end];
            s.trim_right_matches(|c| c == '\r' || c == '\n')
        }

        for (index, c) in input.char_indices() {
            if c == '\n' {
                let s = string_builder(input, start_index, index);
                lines.push((start_index, s));
                start_index = index + 1;
            }
        }

        if start_index != input.len() {
            let s = string_builder(input, start_index, input.len());
            lines.push((start_index, s));
        }

        CodeMap { input_name, lines }
    }


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
}

impl Span {
    pub fn dummy() -> Self {
        Span::new(0, usize::max_value())
    }

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
            end: end.end,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span,
}

impl<T> Spanned<T> {
    pub fn new(inner: T, span: Span) -> Self {
        Spanned { inner, span }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceLocation {
    pub line: usize,
    pub column: usize,
}
