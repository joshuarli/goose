// error: variable B may be used before it is assigned: globals initialize in declaration order
// A parameter default runs at the call, here in A's initializer,
// before B's has run.
var A: i64 = f();
var B: i64[3] = [1, 2, 3];
fn f(x: i64 = B[0]) -> i64 { return x; }
fn main() { print(A); }
