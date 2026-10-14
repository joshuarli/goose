import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
fn view(t: const Tables&) -> View { return View { bytes: t.bytes }; }
fn main() {
    var first: u8[>..] = []; first.append("old");
    var unrelated: u8[>..<] = []; unrelated.append("new");
    var tables = Tables { bytes: first };
    let known = view(tables);
    unrelated.clear();
    print(known.bytes);
}
