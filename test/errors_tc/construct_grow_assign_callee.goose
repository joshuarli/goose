// error: cannot use values in the value assigned to values
// The helper reads the assigned array through its parameter while the
// replacement value is being built.
fn clone_values(values: i64[>..]&) -> i64[>..] {
    return copy(values);
}

fn main() {
    var values: i64[>..] = [1, 2, 3];
    values = clone_values(values);
}
