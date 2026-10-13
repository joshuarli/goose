// error: cannot use values in the value assigned to values
fn main() {
    var values: i64[>..<] = [1, 2];
    values = [values.len];
}
