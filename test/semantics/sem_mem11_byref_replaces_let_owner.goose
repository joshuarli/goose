// Whole-owner replacement through a mutable reference is allowed for a let
// binding whose contents are writable.
fn replace(values: i64[>..<]&) {
    values = [8, 9];
}
fn main() {
    let values: i64[>..<] = [1, 2, 3];
    replace(values);
    print(values.len, " ", values[0], " ", values[1]);
}
