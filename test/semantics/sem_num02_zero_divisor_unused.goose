// A division by zero aborts even when its result is never used. The
// quotient is bound to a local that is never read; an implementation that
// drops dead computations prints "after" and exits normally.
fn main() {
    var zero: i32 = 3;
    zero -= 3;
    print("before");
    let ignored = 10 / zero;
    print("after");
}
