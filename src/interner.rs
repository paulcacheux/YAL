#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InternerId(usize);

#[derive(Debug, Clone, Default)]
pub struct Interner<T> {
    inner: Vec<T>,
}

impl<T: Eq> Interner<T> {
    pub fn new() -> Self {
        Interner {
            inner: Vec::new()
        }
    }

    pub fn intern(&mut self, s: T) -> InternerId {
        for (index, curr_s) in self.inner.iter().enumerate() {
            if &s == curr_s {
                return InternerId(index);
            }
        }

        let index = self.inner.len();
        self.inner.push(s);
        InternerId(index)
    }

    pub fn get_ref(&self, InternerId(index): InternerId) -> &T {
        &self.inner[index]
    }

    pub fn into_vec(self) -> Vec<T> {
        self.inner
    }
}
