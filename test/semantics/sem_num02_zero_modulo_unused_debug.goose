// runtime-define: GS_DEBUG=1
// The remainder by zero aborts in a debug build too, for an unsigned type
// and with the result unused. Division and remainder by zero are checks of
// every build, not of the debug profile.
fn main() {
    var zero: u8 = 5;
    zero -= 5;
    print("before");
    let ignored = 200 % zero;
    print("after");
}
