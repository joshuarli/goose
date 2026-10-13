// error: cannot call drop_last, which shrinks g: the for loop at
// error: iterates g[1..], which may refer into g
// A callee's shrink through a parameter is the caller's.
fn drop_last(a: i64[>..]&) { a.pop(); }
fn main() {
    var g: i64[>..] = [1, 2, 3];
    for x in g[1..] {
        drop_last(g);
        g.push(5);
        print(x);
    }
}
