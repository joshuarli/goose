// error: cannot call reload, which shrinks GA while rr is still used: a reference to a slice that may point into it was stored there
// No global holds a view of GA, but main's holder leads to one through the
// local slice s.
struct R { r: u8[:]& }
var GA: u8[>..] = [];
fn reload() {
    GA.clear();
    GA.append("ZZZZZZZZ");
}
fn main() {
    GA.append("abc");
    var s = GA[..];
    var rr = R { r: s };
    reload();
    print(rr.r);
}
