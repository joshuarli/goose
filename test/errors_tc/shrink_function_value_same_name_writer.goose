// error: cannot clear g while w is still used: it may hold a reference or slice into it
// The block names main's w after it clears g; apply's w is another
// variable.
var g: i64[>..] = [1, 2];
fn apply<F>() -> i64 {
    let n = F();
    let w = 7;
    return n + w;
}
fn main() {
    let w = g[..];
    print(apply() { g.clear(); w.len });
}
