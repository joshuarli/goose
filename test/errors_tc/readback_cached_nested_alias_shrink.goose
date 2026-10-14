// error: cannot clear first while known is still used
import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
struct Nested { view: View }
fn view(t: const Tables&) -> Nested { return Nested { view: View { bytes: t.bytes } }; }
fn main() {
    var first: u8[>..] = [];
    first.append("old");
    var tables = Tables { bytes: first };
    print(view(tables).view.bytes);
    let known = view(tables);
    first.clear();
    first.append("new");
    print(known.view.bytes);
}
