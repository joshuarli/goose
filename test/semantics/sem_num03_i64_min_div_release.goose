// i64.min / -1 aborts in every build, because the quotient does not exist
// in 64 bits; it is not a wrap. The divisions around it succeed: min / 1,
// (min + 1) / -1 and min / 2. A wrong implementation that wraps (as the
// narrower widths do in a release build) prints i64.min and continues.
fn quotient(a: i64, b: i64) -> i64 {
    a / b
}

fn main() {
    let min64 = -9223372036854775807 - 1;
    print(quotient(min64, 1), " ", quotient(min64 + 1, -1), " ", quotient(min64, 2));
    print(quotient(min64, -1));
    print("not reached");
}
