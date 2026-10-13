// error: storing a reference that may point into gs, which holds a grow-shrink array
// Binding a global slice variable stores into a global, which a value
// that may be the view of the grow-shrink gs is not stored in, whatever root
// it kept.
var gs: i64[>..<] = [];
var base: i64[1] = [0];
var gv: i64[:] = base[..];
fn main() {
    gs.push(1);
    let v = if gs.len > 5 { base[..] } else { gs[..] };
    gv = v;
    gs.clear();
    print(gv.len);
}
