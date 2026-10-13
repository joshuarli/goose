// The fixed value is computed before the outer push. Its computation can
// grow the same array, and the returned length is appended after that growth.
fn grow_then_read(values: i64[>..]&) -> i64 {
    values.push(7);
    return values.len;
}

fn main() {
    var values: i64[>..] = [5];
    values.push(grow_then_read(values));
    print(values);
}
