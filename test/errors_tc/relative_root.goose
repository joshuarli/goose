// error: a relative reference must point within the same root as its location
// error: this reference is rooted at other
// A relative reference must derive from the same root as its location.
struct Cell { link: i64&<u16>? }
var pool: Cell[>..] = [];
var other = 5;
fn main() {
    pool.push(Cell { link: other });
}
