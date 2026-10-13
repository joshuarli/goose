// error: cannot clear b while r is still used: it may hold a reference or slice into it
// put stores o into the slot f's parameter names: the load after the call
// may view b, which the clear frees under r.
fn put(q: u8[:]&, o: u8[:]) { q = o; }
fn f(p: u8[:]&, o: u8[:]) -> u8[:] {
    put(p, o);
    return p[0..1];
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
