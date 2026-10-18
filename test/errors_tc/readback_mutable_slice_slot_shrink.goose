// error: while known is still used
import std;
struct Tables { slot: const (const u8[:])& }
struct View { slot: const (const u8[:])& }
fn view(t: const Tables&) -> View { return View { slot: t.slot }; }
fn main() {
    var first: u8[>..] = [];
    first.append("old");
    var slot: const u8[:] = first[..];
    var tables = Tables { slot: slot };
    let known = view(tables);
    var second: u8[>..] = [];
    second.append("new");
    slot = second[..];
    second.clear();
    print(known.slot);
}
