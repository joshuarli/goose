// error: storing a reference rooted at v, which does not outlive the destination
// A [] passed to a slice parameter is a temporary, as a literal with
// elements is, which the callee may not keep a view of.
struct Keep { s: const i64[:] }
var kept = default<Keep>();
fn keep(v: const i64[:]) { kept.s = v; }
fn main() {
    keep([]);
    print(kept.s.len);
}
