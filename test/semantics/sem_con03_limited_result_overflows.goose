// The receiver has only two free slots, so the unknown-length result aborts
// before the append publishes any of its elements.
fn make_values(n: i64) -> i64[] {
    var values: i64[>..] = [];
    for i in n { values.push(5 + i); }
    return values;
}

fn main() {
    var values: i64[..3] = [1];
    print("before ", values);
    values.append(make_values(3));
    print("not reached");
}
