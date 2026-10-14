// error: does not outlive the destination
import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
fn view(t: const Tables&) -> View { return View { bytes: t.bytes }; }
fn main() {
    var known = View { bytes: "" };
    {
        var first: u8[>..] = [];
        first.append("gone");
        var tables = Tables { bytes: first };
        known = view(tables);
    }
    print(known.bytes);
}
