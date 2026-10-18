// error: does not outlive the destination
import std;
struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
fn view(t: const Tables&) -> View { return View { bytes: t.bytes }; }
fn apply<F>(t: const Tables&) { F(view(t)); }
fn main() {
    var known = View { bytes: "" };
    fn store(v: View) { known = v; }
    {
        var first: u8[>..] = [];
        first.append("gone");
        var tables = Tables { bytes: first };
        apply(tables, store);
    }
    print(known.bytes);
}
