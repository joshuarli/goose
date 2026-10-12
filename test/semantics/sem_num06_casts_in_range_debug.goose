// runtime-define: GS_DEBUG=1
// A debug build range-checks `as` only when the value changes. Conversions
// at the boundaries of each target type, widening, and every `as!` (which
// is never checked, even when it changes the value) must not abort. An
// implementation that rejects the boundary value itself, or that checks
// `as!` too, stops before the last line.
fn to_u8(x: i64) -> u8 {
    x as u8
}

fn to_i8(x: i64) -> i8 {
    x as i8
}

fn to_u32(x: i64) -> u32 {
    x as u32
}

fn to_i64(x: u64) -> i64 {
    x as i64
}

fn to_u64(x: i64) -> u64 {
    x as u64
}

fn wide(x: i8) -> i64 {
    let result = x as i64;
    result
}

fn wrap_u8(x: i64) -> u8 {
    x as! u8
}

fn wrap_i8(x: i64) -> i8 {
    x as! i8
}

fn wrap_u64(x: i64) -> u64 {
    x as! u64
}

fn wrap_i64(x: u64) -> i64 {
    x as! i64
}

fn main() {
    print(to_u8(0), " ", to_u8(255), " ", to_i8(-128), " ", to_i8(127), " ", to_u32(4294967295));
    print(to_i64(9223372036854775807), " ", to_u64(0), " ", to_u64(9223372036854775807), " ", wide(-128));
    print(wrap_u8(256), " ", wrap_u8(-1), " ", wrap_i8(128), " ", wrap_i8(-129));
    print(wrap_u64(-1), " ", wrap_i64(18446744073709551615), " ", wrap_i64(9223372036854775808));
}
