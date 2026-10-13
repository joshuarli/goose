// error: returning a reference into a temporary
// copy(x) is a fresh value in a temporary, not x.
var g: i64[3] = [1, 2, 3];
fn pick() -> const i64[:] { copy(g)[..] }
fn main() { print(pick()[0]); }
