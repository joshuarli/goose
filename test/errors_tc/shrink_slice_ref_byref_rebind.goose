// error: cannot clear b while v is still used: it may hold a reference or slice into it
// r refers to s itself, so loading it gives what s holds then:
// a view of b after s is rebound at its root's depth, which the
// clear frees while v still views it.
fn main() {
    var a: u8[>..] = [];
    var b: u8[>..] = [];
    a.append("ab");
    b.append("xyz");
    var s = a[..];
    let r: u8[:]& = s;
    s = b[..];
    let v = r;
    b.clear();
    b.append("QQQ");
    print(v);
}
