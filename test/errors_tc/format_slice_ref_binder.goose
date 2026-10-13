// error: cannot write through this reference: non-writable provenance
// A by-value `for` binding is a copy, never written: a format hook
// taking it by reference takes it as a reference parameter does,
// a read-only reference, however writable the slice it holds.
var buf: u8[>..] = [];
fn format(out: u8[>..]&, p: u8[:]&) { out.append("Q"); p = buf[1..]; }
fn main() {
    buf.append("xyz");
    var arr: u8[:][>..] = [];
    arr.push(buf[..]);
    for s in arr { print(s); }
}
