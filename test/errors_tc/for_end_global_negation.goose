// error: cannot negate a value of unsigned type u8 (convert with `as`)
// A typed range's end naming a constant is a value of the binder's type
// like any bound, checked as the same expression is anywhere: -K
// negates the u8 K, whatever K holds.
let K: u8 = 200;

fn main() {
    for i: i8 in -9..-K {
        print(i);
    }
}
