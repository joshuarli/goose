// error: cannot call read, which shrinks first while known is still used
import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
fn read(out: u8[>..]&) { out.clear(); out.append("x"); }
fn view(t: const Tables&) -> View { return View { bytes: t.bytes }; }
fn main() {
    var first: u8[>..] = [];
    read(first);
    var tables = Tables { bytes: first };
    let known = view(tables);
    read(first);
    print(known.bytes);
}
