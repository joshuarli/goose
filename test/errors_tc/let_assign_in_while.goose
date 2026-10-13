// error: cannot assign to let x, which may be assigned already
// A while loop's next iteration finds x assigned by the one before.
//
fn run(n: i64) {
    let x: i64;
    var i = 0;
    while i < n {
        x = i;
        i += 1;
    }
}
fn main() { run(3); }
