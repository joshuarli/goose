// error: cannot clear b while s is still used: it may hold a reference or slice into it
// inner stores through f's parameter, whose slot is main's s: f's
// call assigns s, which views b when the clear frees it.
fn f(p: u8[:]&, q: u8[:]) {
    fn inner() { p = q; }
    inner();
}
fn main() {
    var a: u8[>..] = [];
    a.append("ab");
    var b: u8[>..] = [];
    b.append("xyz");
    let s = a[..];
    f(s, b[..]);
    b.clear();
    b.append("QQQ");
    print(s);
}
