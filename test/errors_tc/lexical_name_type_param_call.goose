// error: type parameter F is bound to the type i64, not a function
// F is the type parameter, bound here to a type, and hides the global
// function F.
fn F(a: i64) -> i64 { a * 10 }

fn run<F>(a: i64) -> i64 { F(a) }

fn main() { print(run<i64>(1)); }
