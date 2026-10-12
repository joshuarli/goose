// In a release build signed addition, subtraction, multiplication and
// negation wrap in two's complement at the operands' width. A wrong
// implementation that saturates, widens or aborts differs on every line.
fn add8(a: i8, b: i8) -> i8 {
    a + b
}

fn sub8(a: i8, b: i8) -> i8 {
    a - b
}

fn mul8(a: i8, b: i8) -> i8 {
    a * b
}

fn neg8(a: i8) -> i8 { -a
}

fn add16(a: i16, b: i16) -> i16 {
    a + b
}

fn mul16(a: i16, b: i16) -> i16 {
    a * b
}

fn add32(a: i32, b: i32) -> i32 {
    a + b
}

fn sub32(a: i32, b: i32) -> i32 {
    a - b
}

fn mul32(a: i32, b: i32) -> i32 {
    a * b
}

fn add64(a: i64, b: i64) -> i64 {
    a + b
}

fn sub64(a: i64, b: i64) -> i64 {
    a - b
}

fn mul64(a: i64, b: i64) -> i64 {
    a * b
}

fn neg64(a: i64) -> i64 { -a
}

fn main() {
    let min64 = -9223372036854775807 - 1;
    let max64 = 9223372036854775807;
    print(add8(127, 1), " ", sub8(-128, 1), " ", mul8(64, 2), " ", mul8(-128, -1));
    print(neg8(-128), " ", neg8(127), " ", neg8(-127));
    print(add16(32767, 1), " ", mul16(256, 128));
    print(add32(2147483647, 1), " ", sub32(-2147483648, 1), " ", mul32(65536, 65536));
    print(mul32(46341, 46341), " ", mul32(-46341, 46341));
    print(add64(max64, 1), " ", sub64(min64, 1), " ", mul64(max64, 2), " ", mul64(min64, -1));
    print(neg64(min64), " ", neg64(max64));
}
