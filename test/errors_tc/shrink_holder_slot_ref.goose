// error: cannot clear a while rr is still used: a reference to a slice that may point into it was stored there
// rr's field refers to the slice variable s itself, and s views a:
// reading rr.r after the clear reads the storage it freed, which the append
// reuses.
struct R { r: u8[:]& }
fn main() {
    var a: u8[>..] = [];
    a.append("abc");
    var s = a[..];
    var rr = R { r: s };
    a.clear();
    a.append("ZZZZZZZZ");
    print(rr.r);
}
