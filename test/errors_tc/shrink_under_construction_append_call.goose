// error: cannot call mk, which shrinks a: the run appended to a is still under construction, and the shrink would free the storage it is built in
// A call's array result is built at the receiver's top, which the
// call itself may not shrink meanwhile.
fn mk(a: i64[>..]&) -> i64[>..] {
    a.clear();
    var r: i64[>..] = [7, 8];
    return r;
}
fn main() {
    var a: i64[>..] = [1, 2];
    a.append(mk(a));
    print(a);
}
