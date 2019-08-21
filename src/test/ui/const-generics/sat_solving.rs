#![feature(const_generics)]

fn foo<const N: usize>(x: [(); N + N]) -> [(); 2 * N] {
    x
}

fn main() {}
