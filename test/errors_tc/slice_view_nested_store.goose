// error: cannot clear b while r is still used: it may hold a reference or slice into it
// inner stores o through f's parameter into the caller's slot and loads the
// slice back: what it loads may be anything that outlives the slot, b
// included, which the clear frees under r.
fn f(p: u8[:]&, o: u8[:]) -> u8[:] {
    fn inner() -> u8[:] {
        p = o;
        return p[0..1];
    }
    return inner();
}
fn main() {
    var a: u8[>..] = [];
    a.append("abc");
    var b: u8[>..] = [];
    b.append("xyz");
    var s = a[..];
    let r = f(s, b[..]);
    b.clear();
    print(r);
}
