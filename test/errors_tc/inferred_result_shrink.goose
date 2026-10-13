// error: cannot pop a while v (bound at
// An inferred result that is a reference to a non-fixed value is the
// original: popping through it shrinks the caller's array, which a
// view into that array still in use rejects.
struct Ctx { args: i64[>..<]& }
fn args(c: Ctx&) { c.args }
fn f(c: Ctx&) {
    let a = args(c);
    let v = c.args[..];
    a.pop();
    print(v.len);
}
fn main() {
    var s: i64[>..<] = [1, 2];
    var c = Ctx { args: s };
    f(c);
}
