// error: storing a reference into gs, which holds a grow-shrink array
// A view of a grow-shrink array lives only in variables, the one a
// join gives included.
struct Holder { s: const u8[:] }
fn main() {
    var gs: u8[>..<] = [];
    gs.push(65);
    let c = gs.len > 1;
    var h = Holder { s: if c { "x" } else { gs } };
    print(h.s);
}
