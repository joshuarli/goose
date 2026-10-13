// error: the default of field d of S leads to this construction of S, which takes it again
// default<S>() applies S's declared defaults, this one among them.
//
struct S { a: i64 = 1, d: i64 = default<S>().a }
fn main() {
    let x = default<S>();
    print(x.d);
}
