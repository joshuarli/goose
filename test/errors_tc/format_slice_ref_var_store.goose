// error: storing a slice rooted at g into s through format's parameter p
// A format hook taking a slice by reference re-points the variable
// the slice is printed from, as a reference parameter does: it
// stores a view of g into s, which is bound to one of local.
var g: u8[>..] = [];
fn format(out: u8[>..]&, p: u8[:]&) { out.append("Q"); p = g[1..]; }
fn main() {
    g.append("xyz");
    var local: u8[>..] = [];
    local.append("abc");
    var s = local[..];
    print(s);
    g.clear();
    print(s[0]);
}
