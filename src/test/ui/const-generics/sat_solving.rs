// compile-flags: -Ztreat-err-as-bug=1

#![feature(const_generics)] //~ WARN: incomplete

fn foo<const N: usize>(x: [(); N + N]) -> [(); 2 * N] {
    x //~ ERROR: mismatched types
}

fn main() {}
