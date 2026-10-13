// error: returning a reference into a temporary
// A block's value is a copy of its tail's, not the variable the tail names.
//
var g: i64[3] = [1, 2, 3];
fn pick() -> const i64[:] { (block { g })[..] }
fn main() { print(pick()[0]); }
