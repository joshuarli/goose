// runtime-define: GS_DEBUG=1
// A debug build aborts an `as` that only changes the sign: u64 max as i64
// would read as -1, so the value changes. The width is the same, so an
// implementation that checks only narrowing lets it through.
fn to_signed(x: u64) -> i64 {
    x as i64
}

fn main() {
    print(to_signed(9223372036854775807));
    print(to_signed(9223372036854775808));
    print("not reached");
}
