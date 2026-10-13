// error: a let bound to [] can never receive elements; annotate its type, or make it a var
// A let bound to [] can never learn its element type.
fn main() {
    let xs = [];
    print(xs.len);
}
