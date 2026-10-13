// error: cannot infer the element type of []: qput gives it none
// A queue element is sent at its own type, which a [] has none of.
fn main() {
    qput([]);
    print(1);
}
