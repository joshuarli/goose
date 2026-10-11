struct Pair<T> { a: T, b: T }
enum Result<T> { Ok { value: T }, Err }
fn identity<T>(x: T) -> T { x }
fn main() { let x = identity<Pair<i64>>(Pair<i64> { a: 1, b: 2 }); }
