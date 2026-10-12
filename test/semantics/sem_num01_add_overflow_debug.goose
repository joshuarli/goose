// runtime-define: GS_DEBUG=1
// A debug build aborts a signed addition whose true sum is outside the
// width: i8 127 + 1. The line before it, a sum that still fits, is printed;
// the line after it never is. A build that wraps silently continues and
// prints -128.
fn add8(a: i8, b: i8) -> i8 {
    a + b
}

fn main() {
    print(add8(100, 27));
    print(add8(127, 1));
    print("not reached");
}
