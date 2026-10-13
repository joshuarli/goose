// error: storing a reference into p, which holds a grow-shrink array
// A parameter bound to an explicit `&s` of a slice variable stands for the
// slice s holds, so where that slice views a grow-shrink array, what
// is loaded through the parameter may not be stored either.
var G: u8[>..<] = "xyz";
struct K { s: const u8[:] }

fn keep(p: u8[:]&, into: K[>..]&) { into.push(K { s: p }); }

fn main() {
    var hs: K[>..] = [];
    var view: u8[:] = G[..];
    keep(&view, hs);
    G.clear();
    G.append("pqr");
    print(hs[0].s);
}
