// runtime-define: GS_DEBUG=1
// A debug build aborts a signed 64-bit multiplication whose true product is
// outside the range, even when the wrapped result would look harmless: here
// 2^32 * 2^32 wraps to zero, so an implementation that checks only the sign
// or the wrapped value does not abort.
fn mul64(a: i64, b: i64) -> i64 {
    a * b
}

fn main() {
    print(mul64(3037000499, 3037000499));
    print(mul64(4294967296, 4294967296));
    print("not reached");
}
