// core-pilot: legacy-only
fn main() {
    let capacity = 4;
    var values: i64[..] = [..capacity];
    values.push(7);
    print(values.len, " ", values[0]);
}
