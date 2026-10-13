// error: an if used as a value requires an else branch
// An if used as a value requires both arms.
fn main() {
    let c = true;
    let x = if c { 1 };
    print(x);
}
