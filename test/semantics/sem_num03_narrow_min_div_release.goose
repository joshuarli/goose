// In a release build the minimum of a narrower signed width divided by -1 is
// an ordinary overflow and wraps back to the minimum. The next-smaller
// dividend gives the true quotient. A wrong implementation that aborts like
// the 64-bit case, or that widens and keeps the wide quotient 128, differs.
fn div8(a: i8, b: i8) -> i8 {
    a / b
}

fn div16(a: i16, b: i16) -> i16 {
    a / b
}

fn div32(a: i32, b: i32) -> i32 {
    a / b
}

fn main() {
    print(div8(-128, -1), " ", div8(-127, -1), " ", div8(127, -1), " ", div8(-128, 1));
    print(div16(-32768, -1), " ", div16(-32767, -1));
    print(div32(-2147483648, -1), " ", div32(-2147483647, -1));
}
