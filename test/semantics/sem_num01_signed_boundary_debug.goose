// runtime-define: GS_DEBUG=1
// A debug build aborts only on a signed result that is truly out of range.
// Every result here lands exactly on a width's minimum or maximum and must
// be computed without an abort; a check that is off by one prints only the
// first line. Unsigned arithmetic wraps in a debug build as in any other.
fn add8(a: i8, b: i8) -> i8 {
    a + b
}

fn sub8(a: i8, b: i8) -> i8 {
    a - b
}

fn mul8(a: i8, b: i8) -> i8 {
    a * b
}

fn add16(a: i16, b: i16) -> i16 {
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

fn neg8(a: i8) -> i8 { -a
}

fn neg64(a: i64) -> i64 { -a
}

fn wrap_u8(a: u8, b: u8) -> u8 {
    a + b
}

fn wrap_u64(a: u64, b: u64) -> u64 {
    a - b
}

fn main() {
    let min64 = -9223372036854775807 - 1;
    let max64 = 9223372036854775807;
    print(add8(126, 1), " ", add8(-127, -1), " ", sub8(-127, 1), " ", sub8(0, 127));
    print(mul8(-64, 2), " ", mul8(127, 1), " ", mul8(-128, 1), " ", neg8(127));
    print(add16(32766, 1), " ", add16(-32767, -1));
    print(sub32(-2147483647, 1), " ", mul32(46340, 46340), " ", mul32(-2147483648, 1));
    print(add64(max64 - 1, 1), " ", add64(min64 + 1, -1), " ", sub64(min64 + 1, 1));
    print(mul64(max64, 1), " ", mul64(min64, 1), " ", mul64(-4611686018427387904, 2), " ", neg64(max64));
    print(wrap_u8(255, 1), " ", wrap_u64(0, 1));
}
