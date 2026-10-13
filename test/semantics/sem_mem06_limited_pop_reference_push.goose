// A reference to a popped limited-array slot remains valid and sees its next value.
fn main() {
    var xs: i64[..4] = [11, 22];
    let r = &xs[1];
    print(r);
    xs.pop();
    print(r);
    xs.push(33);
    print(r);
}
