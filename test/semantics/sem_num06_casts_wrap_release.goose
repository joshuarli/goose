// In a release build `as` narrows, widens and changes sign by keeping the
// low bits of the source and reinterpreting them at the target width. The
// same values go through `as!`, which must agree. A wrong implementation
// that saturates (255 for 300 as u8, 127 for 200 as i8) or that
// zero-extends a negative source differs.
fn narrow(x: i64) -> u8 {
    x as u8
}

fn narrow_unchecked(x: i64) -> u8 {
    x as! u8
}

fn to_signed8(x: u8) -> i8 {
    x as i8
}

fn to_signed8_unchecked(x: u8) -> i8 {
    x as! i8
}

fn to_unsigned64(x: i64) -> u64 {
    x as u64
}

fn to_signed64(x: u64) -> i64 {
    x as i64
}

fn to_i32(x: i64) -> i32 {
    x as i32
}

fn to_i16(x: i64) -> i16 {
    x as i16
}

fn widen_signed(x: i8) -> i64 {
    let wide = x as i64;
    wide
}

fn widen_unsigned(x: u8) -> i64 {
    let wide = x as i64;
    wide
}

fn main() {
    print(narrow(300), " ", narrow(255), " ", narrow(256), " ", narrow(-1), " ", narrow(-256));
    print(narrow_unchecked(300), " ", narrow_unchecked(-1), " ", narrow_unchecked(511));
    print(to_signed8(200), " ", to_signed8(128), " ", to_signed8(127), " ", to_signed8(255));
    print(to_signed8_unchecked(200), " ", to_signed8_unchecked(128));
    print(to_unsigned64(-1), " ", to_unsigned64(-9223372036854775807 - 1), " ", to_signed64(18446744073709551615));
    print(to_i32(2147483648), " ", to_i32(-2147483649), " ", to_i32(4294967297), " ", to_i16(65537), " ", to_i16(-32769));
    print(widen_signed(-5), " ", widen_signed(-128), " ", widen_unsigned(255), " ", widen_unsigned(128));
}
