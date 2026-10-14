// core-pilot: legacy-only
fn main() {
    let source: i64[2] = [1, 2];
    var values: i64[..4] = source;
    print(values.len, " ", values[0]);
}
