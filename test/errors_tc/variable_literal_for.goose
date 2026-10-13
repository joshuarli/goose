// error: an array literal of variable-size elements is a Txt[]
// A `for` binds references to variable-size elements, so it would
// view a temporary T[] the literal cannot be.
struct Txt { body: u8[] }
fn main() {
    var n = 0;
    for t in [Txt { body: "ab" }, Txt { body: "c" }] { n += t.body.len; }
    print(n);
}
