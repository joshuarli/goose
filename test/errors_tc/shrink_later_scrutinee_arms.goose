// error: cannot call drop, which shrinks a while w is still used: it may hold a reference or slice into it
// A match's arms run after its scrutinee.
fn drop(a: i64[>..]&) -> i64 { a.clear(); return 0; }
fn main() {
    var a: i64[>..] = [1, 2];
    let w = a[..];
    match drop(a) { 0 => print(w), _ => print(1) }
}
