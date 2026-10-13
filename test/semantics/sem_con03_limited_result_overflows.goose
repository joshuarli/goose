// core-pilot: legacy-only
// The result needs three slots, but the limited receiver has only two free.
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
