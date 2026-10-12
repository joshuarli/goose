// runtime-debug
// Shift counts are masked to 0..width-1, so the count -1 acts as width-1 and
// a count of the width or more wraps around: x << 8 is x at i8. Signed >>
// copies the sign bit. Left shifts that move bits out of a signed value do
// not count as overflow, in debug builds either (the first line asks for the
// debug run). A wrong implementation that shifts by the full count prints 0
// for the over-wide counts and, for -1, the C-undefined result.
fn shl8(x: i8, n: i8) -> i8 {
    x << n
}

fn shr8(x: i8, n: i8) -> i8 {
    x >> n
}

fn shl32(x: i32, n: i32) -> i32 {
    x << n
}

fn shr32(x: i32, n: i32) -> i32 {
    x >> n
}

fn shl64(x: i64, n: i64) -> i64 {
    x << n
}

fn shr64(x: i64, n: i64) -> i64 {
    x >> n
}

fn main() {
    print(shl8(1, 0), " ", shl8(1, 7), " ", shl8(1, 8), " ", shl8(1, 9), " ", shl8(1, -1));
    print(shr8(-128, 0), " ", shr8(-128, 7), " ", shr8(-128, 8), " ", shr8(-128, 9), " ", shr8(-128, -1));
    print(shr8(127, 7), " ", shr8(127, 8), " ", shr8(-1, 1), " ", shr8(-1, 100));
    print(shl32(1, 31), " ", shl32(1, 32), " ", shl32(1, 33), " ", shl32(1, -1));
    print(shr32(-2147483648, 31), " ", shr32(-2147483648, 32), " ", shr32(-2147483648, 33));
    print(shl64(1, 63), " ", shl64(1, 64), " ", shl64(1, 65), " ", shl64(1, -1));
    print(shr64(-9223372036854775807 - 1, 63), " ", shr64(-9223372036854775807 - 1, 64), " ", shr64(-8, 66));
}
