// error: type parameter T is bound to the type i64, not a function
// A member call names what a call would, passing over variables only:
// the type parameter T hides the global function T.
fn T(x: i64) -> i64 { x * 100 }

fn f<T>(x: T) -> i64 { x.T() }

fn main() { print(f(2)); }
