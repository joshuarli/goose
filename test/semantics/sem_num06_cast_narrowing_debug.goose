// runtime-define: GS_DEBUG=1
// A debug build aborts a narrowing `as` whose value does not fit the target:
// 256 as u8. 255 on the line before still converts. A build that wraps
// silently prints 0 and continues.
fn to_u8(x: i64) -> u8 {
    x as u8
}

fn main() {
    print(to_u8(255));
    print(to_u8(256));
    print("not reached");
}
