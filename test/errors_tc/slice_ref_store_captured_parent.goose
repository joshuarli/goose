// error: cannot clear b while s is still used: it may hold a reference or slice into it
// inner stores through f's parameter, which names main's s, which f's body
// names as well: the call to inner may assign s, which then
// views b when f clears it.
fn main() {
    var a: u8[>..] = [];
    a.append("ab");
    var b: u8[>..] = [];
    b.append("xyz");
    let s = a[..];
    fn f(p: u8[:]&) {
        fn inner() { p = b[..]; }
        inner();
        b.clear();
        b.append("QQQ");
        print(s);
    }
    f(s);
}
