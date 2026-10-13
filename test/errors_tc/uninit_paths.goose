// error: variable x may be used before it is assigned
// Assigned on only one branch: not definitely assigned after.
fn main() {
    var x: i64;
    let c = true;
    if c { x = 1; }
    print(x);
}
