// error: cannot clear
import std;
reusable[] var pool: u8[>..] = [];
struct Cache { bytes: u8[>..]& }
fn change(cache: Cache&) {
    cache.bytes .= pool;
    cache.bytes.clear();
}
fn main() {
    var bytes: u8[>..] = [];
    var cache = Cache { bytes: bytes };
    change(cache);
}
