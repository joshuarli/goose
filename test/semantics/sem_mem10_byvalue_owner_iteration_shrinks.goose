// A by-value owner iteration snapshots each fixed element before the body,
// so shrinking the owner cannot invalidate that snapshot.
fn main() {
    var values: i64[>..<] = [1, 2, 3];
    var total = 0;
    for item in values {
        values.pop();
        total += item;
    }
    print(total, " ", values.len, " ", values[0]);
}
