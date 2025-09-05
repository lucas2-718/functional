use crate::ctypes::ContainedTerm;

struct Pattern {
    data: Vec<String>,
}

struct Notation {
    pattern: Pattern,
    term: ContainedTerm
}