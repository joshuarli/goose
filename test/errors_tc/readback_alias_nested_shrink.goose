// error: cannot clear first while known is still used
import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
fn view(t: const Tables&) -> View { return View { bytes: t.bytes }; }
fn main() {
    var first: u8[>..] = [];
    first.append("old");
    var tables = Tables { bytes: first };
    let known = view(tables);
    fn clear() { first.clear(); }
    clear();
    first.append("new");
    print(known.bytes);
}
