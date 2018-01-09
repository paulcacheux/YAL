#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringId(usize);

#[derive(Debug, Clone, Default)]
pub struct StringInterner {
    strs: Vec<String>,
}

impl StringInterner {
    pub fn new() -> StringInterner {
        StringInterner::default()
    }

    pub fn intern(&mut self, s: String) -> StringId {
        for (index, curr_s) in self.strs.iter().enumerate() {
            if &s == curr_s {
                return StringId(index);
            }
        }

        let index = self.strs.len();
        self.strs.push(s);
        StringId(index)
    }

    pub fn get_str(&self, StringId(index): StringId) -> &str {
        &self.strs[index][..]
    }

    pub fn into_strings(self) -> Vec<String> {
        self.strs
    }

    /*pub fn get_string(&self, StringId(index): StringId) -> String {
        self.strs[index].clone()
    }*/
}
