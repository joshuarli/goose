// error: operands of + have no common type: u32 and i32 (convert one with `as`)
// Same-width signed/unsigned operands have no common type.
fn main() {
    var a: u32 = 1;
    var b: i32 = 2;
    print(a + b);
}
