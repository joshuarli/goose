// runtime-define: GS_DEBUG=1
// The same i64.min / -1 abort, with the same diagnostic, in a debug build:
// the 64-bit case is a division failure in every build, not a debug
// overflow check.
fn quotient(a: i64, b: i64) -> i64 {
    a / b
}

fn main() {
    let min64 = -9223372036854775807 - 1;
    print(quotient(min64 + 1, -1));
    print(quotient(min64, -1));
    print("not reached");
}
