fn first() -> i64 { print("first"); 1 }
fn stop() -> i64 { print("stop"); abort("middle") }
fn last() -> i64 { print("last "); 3 }

struct Ordered { a: i64 = first(), b: i64 = stop(), c: i64 = last() }

fn main() {
    let value = Ordered {};
    print("complete", value);
}
