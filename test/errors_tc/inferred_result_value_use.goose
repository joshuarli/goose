// error: args(c) is not fixed-size and is not copied implicitly (§4.1): pass copy(args(c)) for a copy
// A result inferred from a reference to a non-fixed value is that reference,
// which a value-typed destination takes only as an explicit copy.
//
struct Ctx { args: i64[>..<]& }
fn args(c: Ctx&) { c.args }
fn main() {
    var s: i64[>..<] = [1];
    var c = Ctx { args: s };
    let v: i64[>..<] = args(c);
    print(v);
}
