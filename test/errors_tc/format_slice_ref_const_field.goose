// error: cannot write through this reference: non-writable provenance
// A field of a `const` value is not written: a format hook taking
// it by reference gets a read-only reference, as `&c.f` is.
struct P { x: i64 }
struct S { f: P[:] }
var buf: P[>..] = [];
fn format(out: u8[>..]&, p: P[:]&) { out.append("P"); p = buf[1..]; }
fn main() {
    buf.push(P { x: 1 });
    buf.push(P { x: 2 });
    const c = S { f: buf[..] };
    print(c.f);
}
