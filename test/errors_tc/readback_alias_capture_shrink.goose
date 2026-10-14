// error: shrinks first while known is still used
import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
fn view(t: const Tables&) -> View { return View { bytes: t.bytes }; }
fn read(out: u8[>..]&) { out.clear(); out.append("new"); }
fn apply<F>() { F(); }
fn main() {
    var first: u8[>..] = [];
    first.append("old");
    var tables = Tables { bytes: first };
    let known = view(tables);
    apply() { read(first); };
    print(known.bytes);
}
