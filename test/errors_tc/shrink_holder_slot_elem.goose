// error: cannot clear a while rr is still used: a reference to a slice that may point into it was stored there
// rr's field refers to an element of ss, a slice the push made a
// view of a.
struct R { r: u8[:]& }
fn main() {
    var a: u8[>..] = [];
    a.append("abc");
    var ss: (u8[:])[>..] = [];
    ss.push(a[..]);
    var rr = R { r: ss[0] };
    a.clear();
    a.append("ZZZZZZZZ");
    print(rr.r);
}
