// runtime-define: GS_DEBUG=1
// A debug build aborts an `as` of a negative signed value to an unsigned
// type, even to the widest one: -1 as u64 would read as 2^64 - 1.
fn to_unsigned(x: i32) -> u64 {
    x as u64
}

fn main() {
    print(to_unsigned(0));
    print(to_unsigned(-1));
    print("not reached");
}
