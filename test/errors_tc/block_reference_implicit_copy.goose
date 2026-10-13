// error: c.args is not fixed-size and is not copied implicitly
// A bare block's value is a copy of its tail's, a reference's non-fixed
// pointee included.
struct Ctx { args: i64[>..<]& }
fn main() {
    var s: i64[>..<] = [];
    var c = Ctx { args: s };
    let q = { c.args };
    q.push(5);
    print(s.len);
}
