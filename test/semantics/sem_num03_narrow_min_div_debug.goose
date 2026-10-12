// runtime-define: GS_DEBUG=1
// In a debug build the same i8 case is an overflow check: -128 / -1 aborts
// with the overflow diagnostic, not the division one. The preceding lines
// show the quotients that fit.
fn div8(a: i8, b: i8) -> i8 {
    a / b
}

fn main() {
    print(div8(-127, -1), " ", div8(127, -1), " ", div8(-128, 1));
    print(div8(-128, -1));
    print("not reached");
}
