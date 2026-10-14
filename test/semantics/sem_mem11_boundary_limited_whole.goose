// core-pilot: legacy-only
fn main() {
    var values: i64[..4] = [1, 2];
    values = [3];
    print(values.len, " ", values[0]);
}
