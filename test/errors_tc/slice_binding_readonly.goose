// error: storing a read-only slice of type const u8[:] in a slot of type u8[:]
// A const array's whole-array slice is read-only.
const TABLE: u8[3] = [7, 8, 9];
fn main() {
    let s: u8[:] = TABLE;
    print(s);
}
