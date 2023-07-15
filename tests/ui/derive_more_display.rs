//@run-rustfix
#![feature(rustc_private)]
#![allow(unused)]
#![warn(clippy::derive_more_display)]

extern crate derive_more;

mod x {
    impl std::fmt::Display for Type {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            write!(f, "{:?}, world {}", self.first, self.second.0)
        }
    }

    struct X {}

    struct Type {
        first: usize,
        second: (usize, usize),
    }
}

fn main() {}
