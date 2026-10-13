// error: varint fields are written only at construction
// varint fields are written only at construction.
struct S { v: varint }
fn main() {
    var s = S { v: 1 };
    s.v = 2;
}
