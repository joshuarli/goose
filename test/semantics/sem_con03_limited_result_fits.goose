// core-pilot: legacy-only
// A runtime-sized result fills the limited receiver's remaining capacity.
fn make_values(n: i64) -> i64[] {
    var values: i64[>..] = [];
    for i in n { values.push(5 + i); }
    return values;
}

fn main() {
    var values: i64[..4] = [1];
    values.append(make_values(3));
    print(values, " ", values.len, " ", values.cap);
}
