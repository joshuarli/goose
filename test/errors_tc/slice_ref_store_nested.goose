// error: cannot clear b while s is still used: it may hold a reference or slice into it
// inner stores through main's reference to s, which assigns s:
// s views b when the clear frees it.
fn main() {
    var a: u8[>..] = [];
    a.append("ab");
    var b: u8[>..] = [];
    b.append("xyz");
    let s = a[..];
    let r = &s;
    fn inner() { r = b[..]; }
    inner();
    b.clear();
    b.append("QQQ");
    print(s);
}
