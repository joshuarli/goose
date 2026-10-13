// error: cannot call drop, which shrinks xs while s
// error: is still used: it may refer into xs (§5.2)
fn drop(xs: i64[>..<]&) {
    xs.pop();
}

fn main() {
    var xs: i64[>..<] = [1, 2];
    let s = xs[..];
    drop(xs);
    print(s[0]);
}
