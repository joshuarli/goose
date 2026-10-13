// core-pilot: legacy-only
// A different owner can grow while the receiver's nonfixed element is built.
fn make(other: i64[>..]&) -> i64[] {
    other.push(7);
    return[8, 9];
}

fn main() {
    var rows: i64[][>..] = [];
    var other: i64[>..] = [];
    rows.push(make(other));
    print("rows ", rows.len);
    for row in rows {
        print("row ", row);
    }
    print("other ", other.len, " ", other[0]);
}
