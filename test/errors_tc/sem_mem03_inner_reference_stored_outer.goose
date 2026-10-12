// error: storing a reference rooted at inner, which does not outlive the destination
// A reference variable declared in the outer scope may not be rebound to a
// variable that dies when the inner block ends.
fn main() {
    var outer: i64 = 1;
    var kept .= outer;
    {
        var inner: i64 = 2;
        kept .= inner;
    }
    print(kept);
}
