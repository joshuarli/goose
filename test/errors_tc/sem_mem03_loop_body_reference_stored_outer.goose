// error: storing a reference rooted at element, which does not outlive the destination
// A variable declared in a loop body is a new variable on every iteration and
// dies with it, so the outer reference may not be rebound to it.
fn main() {
    var seed: i64 = 0;
    var kept .= seed;
    for i in 0..3 {
        var element: i64 = i;
        kept .= element;
    }
    print(kept);
}
