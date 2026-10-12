// runtime-debug
// Remainder at the extremes. Dividing a minimum by -1 has remainder 0 and
// does not trap (the quotient would overflow, the remainder does not).
// i64.min % i64.max is i64.max - 1, because the dividend is -1 * i64.max - 1
// and the remainder is made nonnegative; a truncating remainder gives -1.
// The debug build must agree (the first line asks for it).
fn remainder(a: i64, b: i64) -> i64 {
    a % b
}

fn remainder8(a: i8, b: i8) -> i8 {
    a % b
}

fn remainder32(a: i32, b: i32) -> i32 {
    a % b
}

fn main() {
    let min64 = -9223372036854775807 - 1;
    let max64 = 9223372036854775807;
    print(remainder(min64, -1), " ", remainder8(-128, -1), " ", remainder32(-2147483648, -1));
    print(remainder(min64, max64), " ", remainder(min64, min64), " ", remainder(max64, min64));
    print(remainder(-1, min64), " ", remainder(min64, 2), " ", remainder(min64 + 1, 2));
}
