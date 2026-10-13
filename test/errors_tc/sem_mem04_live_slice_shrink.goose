// error: cannot pop xs while s
// error: is still used: it may refer into xs (§5.2)
fn main() {
    var xs: i64[>..<] = [1, 2];
    let s = xs[..];
    xs.pop();
    print(s[0]);
}
