// runtime-debug
import std;

struct Tables { bytes: const u8[:] }
struct View { bytes: const u8[:] }

fn view(t: const Tables&) -> View {
    return View { bytes: t.bytes };
}

fn read(out: u8[>..]&) {
    out.clear();
    out.append("new");
}

fn main() {
    var first: u8[>..] = [];
    first.append("kept");
    var tables = Tables { bytes: first };
    let known = view(tables);
    var second: u8[>..] = [];
    read(second);
    print(known.bytes, " ", second);
}
