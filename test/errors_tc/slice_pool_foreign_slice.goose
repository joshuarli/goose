// error: .free_slice needs a slice of the pool it is called on
// error: this one is rooted at other
// A slice exactly rooted at another array this function owns cannot be one of
// the pool's runs, so it is refused before the program runs.
fn main() {
    reusable[] var pool: i64[>..] = [];
    var other: i64[>..] = [1, 2, 3];
    pool.free_slice(other[0..2]);
}
