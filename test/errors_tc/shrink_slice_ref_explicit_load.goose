// error: cannot clear gs while v
// error: is still used: it may refer into gs
// The slice loaded through `&s` is s's slice, rooted where s points, not at
// the variable s.
fn main() {
    var gs: i64[>..<] = [42];
    var s = gs[..];
    let p = &s;
    let v = p;
    gs.clear();
    print(v[0]);
}
