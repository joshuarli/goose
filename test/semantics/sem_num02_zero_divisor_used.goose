// A zero divisor aborts with a division diagnostic, and the output written
// before the division stays written. The divisor reaches the division only
// through a parameter, so no constant folding can hide it. A wrong
// implementation that yields 0 or a trap value continues and prints more.
fn quotient(a: i64, b: i64) -> i64 {
    a / b
}

fn main() {
    print("before");
    print(quotient(9, 3), " ", quotient(0, 7), " ", quotient(-9, 4));
    print(quotient(5, 0));
    print("not reached");
}
