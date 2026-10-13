// error: integer match requires a _ arm
// Integer matches require a _ arm.
fn main() {
    let v = match 3 { 0 => 1, 1..10 => 2 };
    print(v);
}
