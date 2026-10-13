// error: cannot write through this reference: non-writable provenance
// A by-value `match` binding is a copy, never written, and so are its
// fields: bound by reference, one is a read-only reference.
enum E { A { s: u8[:] }, B { k: i64 } }
var buf: u8[>..] = [];
fn set(q: u8[:]&) { q = buf[1..]; }
fn main() {
    buf.append("xyz");
    let e: E = E.A { s: buf[..] };
    match e { A a => { set(a.s); print(a.s); }, B b => {} }
}
