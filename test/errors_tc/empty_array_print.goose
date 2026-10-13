// error: cannot infer the element type of []: print gives it none
// print renders a value at its own type, which a [] has none of.
fn main() {
    print([]);
}
