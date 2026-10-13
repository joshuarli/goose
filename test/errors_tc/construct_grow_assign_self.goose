// error: cannot use values in the value assigned to values: that value is built over the old contents of values
// The new value is built over the array's old storage, so it cannot read
// that array while the assignment is being constructed.
fn main() {
    var values: i64[>..] = [1, 2, 3];
    values = copy(values);
    print(values);
}
