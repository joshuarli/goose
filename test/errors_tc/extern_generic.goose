// error: extern fn ident cannot be generic
// extern fns are fully typed and not generic.
extern fn ident<T>(x: T) -> T;
fn main() { print(ident(1)); }
