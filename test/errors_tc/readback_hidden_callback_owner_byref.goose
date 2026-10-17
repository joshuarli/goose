// error: cannot clear first while known is still used
import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
fn view(t: const Tables&) -> View { return View { bytes: t.bytes }; }
fn apply<F>() {
    var first: u8[>..] = [];
    first.append("old");
    var tables = Tables { bytes: first };
    F(&tables);
}
fn main() {
    apply() { incoming =>
        var local = Tables { bytes: incoming.bytes };
        let known = view(local);
        incoming.bytes.clear();
        print(known.bytes);
    };
}
