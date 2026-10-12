// The caller holds a reference to an element and passes the array on by
// reference. The callee overwrites that element; the reference stays valid
// and reads the new value, and so does a slice the caller holds of the same
// element. An implementation that passes the array by copy leaves the
// element at its old value.
fn overwrite(items: i64[>..]&, value: i64) {
    items[1] = value;
}

fn main() {
    var items: i64[>..] = [1, 2, 3];
    let held .= items[1];
    let view = items[1..3];
    print(held, " ", view[0]);
    overwrite(items, 20);
    print(held, " ", view[0], " ", items[1]);
}
