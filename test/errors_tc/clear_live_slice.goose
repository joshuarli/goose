// error: cannot clear buf while s is still used: it may hold a reference or slice into it
// A slice into a grow-only local is live at the clear.
fn main() {
    var buf: u8[>..] = [];
    buf.append("ab");
    let s = buf[0..2];
    buf.clear();
    print(s.len);
}
