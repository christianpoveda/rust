// build-pass

#![feature(const_generics)] //~ WARN: incomplete

fn foo<const N: usize>(x: [(); N + N]) -> [(); 2 * N] {
    x
}

fn main() {
    let y = foo([(), (), (), ()]);
}
